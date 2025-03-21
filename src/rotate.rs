// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::fs::File;
use std::fs::remove_file;
use std::fs::rename;
use std::io;
use std::io::BufRead as _;
use std::io::BufReader;
use std::io::ErrorKind;
use std::io::SeekFrom;
use std::io::Write as _;
use std::os::fd::AsRawFd as _;
use std::os::fd::FromRawFd as _;
use std::os::fd::IntoRawFd as _;
use std::os::fd::OwnedFd;
use std::path::Path;
use std::path::PathBuf;

use anyhow::Context as _;
use anyhow::Result;

use libc::O_CLOEXEC;
use libc::dup3;

use log::warn;

use crate::util::check;


fn count_file_lines<F>(file: &mut F) -> Result<usize>
where
  F: io::Read + io::Seek,
{
  let position = file
    .stream_position()
    .context("failed to determine file cursor position")?;
  let () = file.rewind().context("failed to rewind file cursor")?;
  let mut reader = BufReader::new(&mut *file);

  let mut lines = 0;
  let result = loop {
    let mut line = Vec::new();
    match reader.read_until(b'\n', &mut line) {
      Ok(0) => break Ok(lines),
      Ok(_) => {
        lines += 1;
        let () = line.clear();
      },
      Err(err) => break Err(err),
    }
  };

  // Restore initial file cursor position.
  let _position = file
    .seek(SeekFrom::Start(position))
    .context("failed to restore file cursor position")?;
  debug_assert_eq!(_position, position);

  Ok(result?)
}

// Note that this function does not always report exactly the same line
// count as `count_file_lines` would -- differences of +/- 1 are
// possible.
fn count_buffer_lines(buffer: &[u8]) -> usize {
  buffer.iter().filter(|b| *b == &b'\n').count()
}


#[derive(Debug, Default)]
pub(crate) struct Builder {
  max_lines: Option<usize>,
  max_files: Option<usize>,
}

impl Builder {
  /// Set the maximum number of lines in a file.
  ///
  /// # Notes
  /// Please note that this limit is not necessarily painstakingly
  /// enforced. It is more seen as a hint of roughly how many lines to
  /// allow in a file before rotating the file.
  ///
  /// # Panics
  /// This function panics on an attempt to set the line limit to `0`.
  pub fn set_max_lines(mut self, max_lines: Option<usize>) -> Self {
    assert_ne!(max_lines, Some(0));
    self.max_lines = max_lines;
    self
  }

  /// # Panics
  /// This function panics on an attempt to set the file limit to `0`.
  pub fn set_max_files(mut self, max_files: Option<usize>) -> Self {
    assert_ne!(max_files, Some(0));
    self.max_files = max_files;
    self
  }

  pub fn build<P>(self, path: P) -> Result<Rotate>
  where
    P: AsRef<Path>,
  {
    fn build_impl(slf: Builder, path: &Path) -> Result<Rotate> {
      let Builder {
        max_lines,
        max_files,
      } = slf;

      let max_lines = max_lines.unwrap_or(1000);
      let max_files = max_files.unwrap_or(10);

      #[allow(clippy::ineffective_open_options)]
      let mut file = File::options()
        .create(true)
        .read(true)
        .write(true)
        .append(true)
        .open(path)
        .with_context(|| format!("failed to open file `{}`", path.display()))?;

      let lines = count_file_lines(&mut file)
        .with_context(|| format!("failed to count lines of `{}`", path.display()))?;

      let mut slf = Rotate {
        inner: RotateInner {
          path: path.to_path_buf(),
          file: Some(file),
          lines,
          max_lines,
          max_files,
        },
        buffer: Box::new([0; 512]),
      };

      if lines >= max_lines {
        // TODO: May have to rotate multiple times, strictly speaking,
        //       as a pre-existing could have any number of lines.
        let () = slf.inner.rotate()?;
      }
      Ok(slf)
    }

    build_impl(self, path.as_ref())
  }
}


#[derive(Debug)]
struct RotateInner {
  /// The path of the currently open log file.
  path: PathBuf,
  /// The currently open log file.
  file: Option<File>,
  /// The number of lines currently in the file.
  lines: usize,
  /// The maximum number of lines in the file, before a rotation
  /// happens.
  max_lines: usize,
  /// The maximum number of files to keep around.
  ///
  /// This includes the one currently open, meaning that for a value of
  /// `10` nine additional files will be kept at a maximum.
  max_files: usize,
}

impl RotateInner {
  fn suffix_digits(&self) -> usize {
    // Account for the fact that the "main" file does not have a suffix.
    let files = self.max_files.saturating_sub(1);
    let digits = files.checked_ilog10().unwrap_or(0) as usize + 1;
    digits
  }

  fn rotate(&mut self) -> Result<()> {
    let digits = self.suffix_digits();
    let revert_rename = |n| {
      for i in 0..n {
        let mut src = self.path.clone();
        let () = src.push(format!("{:digits$}", i + 1));

        let mut dst = self.path.clone();
        if i != 0 {
          let () = dst.push(format!("{:digits$}", i));
        }

        if let Err(err) = rename(&src, &dst) {
          warn!(
            "failed to rename `{}` back to `{}`: {err:#}",
            src.display(),
            dst.display()
          );
        }
      }
    };

    let mut max_found = 0;
    // Rotate all "archived" files.
    for i in (0..self.max_files).rev() {
      let mut src = self.path.clone();
      if i != 0 {
        let () = src.as_mut_os_string().push(format!(".{:digits$}", i));
      }

      let mut dst = self.path.clone();
      let () = dst.as_mut_os_string().push(format!(".{:digits$}", i + 1));

      // TODO: Consider making the "archived" files read-only as well.
      // TODO: Consider adding compression support.
      match rename(&src, &dst) {
        Ok(()) => {
          if max_found == 0 {
            max_found = i;
          }
        },
        Err(err) if err.kind() == ErrorKind::NotFound => (),
        Err(err) => {
          // On actual error we attempt to revert all the renames, but
          // that's pretty much the best we can do (short of backing up
          // the originals, perhaps, which was considered too
          // expensive considering the minimal value it provides).
          let () = revert_rename(max_found);
          return Err(err).with_context(|| {
            format!(
              "failed to rename `{}` to `{}`",
              src.display(),
              dst.display()
            )
          })
        },
      }
    }

    let mut rest = || {
      let new_file = File::options()
        .create_new(true)
        .write(true)
        .open(&self.path)
        .with_context(|| format!("failed to create file `{}`", self.path.display()))?;
      let new_fd = OwnedFd::from(new_file);
      // SANITY: This is the only location where we `take` the file and
      //         we always put it back, so it has to be present right
      //         now.
      let old_fd = self.file.take().unwrap().into_raw_fd();

      // SAFETY: `dup3` is always safe to call.
      let rc = unsafe { dup3(new_fd.as_raw_fd(), old_fd, O_CLOEXEC) };
      // Reconstitute the file from the file descriptor. On success of
      // the `dup3` it now refers to the new file, on error it should
      // still refer to the old one and we attempt to roll back
      // everything else.
      // SAFETY: `old_fd` is an owned open file descriptor.
      self.file = Some(unsafe { File::from_raw_fd(old_fd) });
      let () = check(rc, -1).context("failed to dup3 file descriptor")?;

      self.lines = 0;

      // If everything was successful and we had already `max_files`
      // before the rotation, we should make sure to delete the last
      // addition, which now actually exceeds this limit.
      // Note that this operation could conceivably delete a file not
      // actually created by the rotation logic, but by design we treat
      // every file matching our file-creation pattern as managed by us.
      let mut last = self.path.clone();
      let () = last
        .as_mut_os_string()
        .push(format!(".{:digits$}", self.max_files));
      let _result = remove_file(&last);

      Ok(())
    };

    let result = rest();
    if result.is_err() {
      let () = revert_rename(max_found);
    }
    result
  }

  fn write_impl(&mut self, data: &[u8]) -> Result<()> {
    // We don't treat our `max_lines` as a hard limit: we write out the
    // entirety of the data before checking for the need of file
    // rotation, this means we could theoretically overshoot. In
    // reality, 99% of the time only a single line will be read anyway,
    // because clients are not expected to emit huge swaths of data to
    // begin with, and so sporadic single line messages should be the
    // norm.
    let () = self
      .file
      .as_mut()
      // SANITY: The file is only ever temporarily unset.
      .unwrap()
      .write_all(data)
      .context("failed to forward data to file")?;

    let lines = count_buffer_lines(data);
    self.lines += lines;

    if self.lines >= self.max_lines {
      let () = self.rotate()?;
    }
    Ok(())
  }
}


#[derive(Debug)]
pub(crate) struct Rotate {
  inner: RotateInner,
  /// Heap allocated buffer used when reading data to forward to the
  /// file from a source.
  buffer: Box<[u8; 512]>,
}

impl Rotate {
  pub fn builder() -> Builder {
    Builder::default()
  }

  /// Forward data from a reader to the file, potentially rotating it if
  /// a limit is reached.
  ///
  /// In many ways this method acts like `std::io::copy` from the
  /// provided source to the file we represent, except that it doesn't
  /// attempt reading the stream to EOF (which likely would involved
  /// blocking), but just until we fail reading a full buffer's worth of
  /// data.
  pub fn forward<R>(&mut self, read: &mut R) -> Result<()>
  where
    R: io::Read,
  {
    loop {
      let count = read
        .read(self.buffer.as_mut_slice())
        .context("failed to read new data")?;
      let data = &self.buffer[0..count];

      let () = self.inner.write_impl(data)?;

      // If we didn't read a whole buffer's worth of data we assume that
      // right now no more data is available and stop here.
      if count < self.buffer.len() {
        break Ok(())
      }
    }
  }
}

impl io::Write for Rotate {
  fn write(&mut self, data: &[u8]) -> io::Result<usize> {
    match self.inner.write_impl(data) {
      Ok(()) => Ok(data.len()),
      Err(err) => {
        let cause = err.root_cause();
        let kind = cause
          .downcast_ref::<io::Error>()
          .map(io::Error::kind)
          .unwrap_or(io::ErrorKind::Other);
        Err(io::Error::new(kind, cause.to_string()))
      },
    }
  }

  fn flush(&mut self) -> io::Result<()> {
    self.inner.file.as_mut().unwrap().flush()
  }
}


#[cfg(test)]
mod tests {
  use super::*;

  use std::fs::read;
  use std::fs::write;
  use std::io::Cursor;

  use tempfile::tempdir;


  /// Check that we can count lines in a "file" properly.
  #[test]
  fn line_counting() {
    let lines = b"";
    assert_eq!(count_file_lines(&mut Cursor::new(lines)).unwrap(), 0);
    assert_eq!(count_buffer_lines(lines), 0);

    let lines = b"first
      second
";
    assert_eq!(count_file_lines(&mut Cursor::new(lines)).unwrap(), 2);
    assert_eq!(count_buffer_lines(lines), 2);

    let lines = b"a
whole
slew
of
lines
";
    let mut cursor = Cursor::new(lines);
    assert_eq!(count_file_lines(&mut cursor).unwrap(), 5);
    assert_eq!(count_buffer_lines(lines), 5);
    // Also make sure that the cursor is back at the beginning.
    assert_eq!(&cursor.get_ref()[0..4], b"a\nwh");
  }

  /// Check that data "forwarded" to our file ends up where it should,
  /// even after a file rotation.
  #[test]
  fn forward_rotation() {
    let dir = tempdir().unwrap();
    let log = dir.path().join("file.log");
    let log1 = dir.path().join("file.log.1");
    let log2 = dir.path().join("file.log.2");

    let mut rotate = Rotate::builder()
      .set_max_files(Some(3))
      .build(&log)
      .unwrap();
    assert_eq!(read(&log).unwrap(), b"");
    assert!(!log1.try_exists().unwrap());
    assert!(!log2.try_exists().unwrap());

    let () = rotate.forward(&mut b"log\n".as_slice()).unwrap();
    let () = rotate.inner.file.as_mut().unwrap().flush().unwrap();

    assert_eq!(read(&log).unwrap(), b"log\n");
    assert!(!log1.try_exists().unwrap());
    assert!(!log2.try_exists().unwrap());

    // Force a rotation.
    let () = rotate.inner.rotate().unwrap();
    assert_eq!(read(&log).unwrap(), b"");
    assert_eq!(read(&log1).unwrap(), b"log\n");
    assert!(!log2.try_exists().unwrap());

    // Make sure new data ends up in the new log file.
    let () = rotate.forward(&mut b"next-log\n".as_slice()).unwrap();
    let () = rotate.inner.file.as_mut().unwrap().flush().unwrap();

    assert_eq!(read(&log).unwrap(), b"next-log\n");
    assert_eq!(read(&log1).unwrap(), b"log\n");
    assert!(!log2.try_exists().unwrap());
  }

  /// Make sure that file rotation does not accumulate more than the
  /// maximum number of files.
  #[test]
  fn rotation_max_files() {
    {
      let dir = tempdir().unwrap();
      let log = dir.path().join("file.log");
      let () = write(&log, b"log\n").unwrap();
      let log1 = dir.path().join("file.log.1");
      let log2 = dir.path().join("file.log.2");
      let log3 = dir.path().join("file.log.3");

      let mut rotate = Rotate::builder()
        .set_max_files(Some(3))
        .build(&log)
        .unwrap();
      let () = rotate.inner.rotate().unwrap();

      assert_eq!(read(&log).unwrap(), b"");
      assert_eq!(read(&log1).unwrap(), b"log\n");
      assert!(!log2.try_exists().unwrap());
      assert!(!log3.try_exists().unwrap());
    }

    {
      let dir = tempdir().unwrap();
      let log = dir.path().join("file.log");
      let () = write(&log, b"log\n").unwrap();
      let log1 = dir.path().join("file.log.1");
      let () = write(&log1, b"log1\n").unwrap();
      let log2 = dir.path().join("file.log.2");
      let log3 = dir.path().join("file.log.3");

      let mut rotate = Rotate::builder()
        .set_max_files(Some(3))
        .build(&log)
        .unwrap();
      let () = rotate.inner.rotate().unwrap();

      assert_eq!(read(&log).unwrap(), b"");
      assert_eq!(read(&log1).unwrap(), b"log\n");
      assert_eq!(read(&log2).unwrap(), b"log1\n");
      assert!(!log3.try_exists().unwrap());
    }

    {
      let dir = tempdir().unwrap();
      let log = dir.path().join("file.log");
      let () = write(&log, b"log\n").unwrap();
      let log1 = dir.path().join("file.log.1");
      let () = write(&log1, b"log1\n").unwrap();
      let log2 = dir.path().join("file.log.2");
      let () = write(&log2, b"log2\n").unwrap();
      let log3 = dir.path().join("file.log.3");

      let mut rotate = Rotate::builder()
        .set_max_files(Some(3))
        .build(&log)
        .unwrap();
      let () = rotate.inner.rotate().unwrap();

      assert_eq!(read(&log).unwrap(), b"");
      assert_eq!(read(&log1).unwrap(), b"log\n");
      assert_eq!(read(&log2).unwrap(), b"log1\n");
      assert!(!log3.try_exists().unwrap());
    }

    {
      let dir = tempdir().unwrap();
      let log = dir.path().join("file.log");
      let () = write(&log, b"log\n").unwrap();
      let log1 = dir.path().join("file.log.1");
      let () = write(&log1, b"log1\n").unwrap();
      let log2 = dir.path().join("file.log.2");
      let () = write(&log2, b"log2\n").unwrap();
      let log3 = dir.path().join("file.log.3");
      let () = write(&log3, b"log3\n").unwrap();

      let mut rotate = Rotate::builder()
        .set_max_files(Some(3))
        .build(&log)
        .unwrap();
      let () = rotate.inner.rotate().unwrap();

      assert_eq!(read(&log).unwrap(), b"");
      assert_eq!(read(&log1).unwrap(), b"log\n");
      assert_eq!(read(&log2).unwrap(), b"log1\n");
      assert!(!log3.try_exists().unwrap());
    }
  }

  /// Test that we perform a file rotation if the to-open file is
  /// already at or beyond the maximum line limit.
  #[test]
  fn immediate_rotation() {
    let dir = tempdir().unwrap();
    let log = dir.path().join("file.log");
    let () = write(&log, b"three\nline\ncontent\n").unwrap();

    let _rotate = Rotate::builder()
      .set_max_lines(Some(2))
      .build(&log)
      .unwrap();

    assert_eq!(read(&log).unwrap(), b"");
    let log1 = dir.path().join("file.log.1");
    assert_eq!(read(&log1).unwrap(), b"three\nline\ncontent\n");
  }

  /// Test the end-to-end workflow of writing a bunch of lines to a
  /// `Rotate` object.
  #[test]
  fn extensive_line_writing() {
    let dir = tempdir().unwrap();
    let log = dir.path().join("file.log");

    let mut rotate = Rotate::builder()
      .set_max_lines(Some(4))
      .set_max_files(Some(4))
      .build(&log)
      .unwrap();

    for i in 1..=1000 {
      let line = format!("{i}\n");
      let _count = rotate.write(line.as_bytes()).unwrap();
    }
    let () = drop(rotate);

    // Because 1000 is evenly divisible by our `max_lines`, the current
    // log file will just have experienced a rotation and be empty.
    assert_eq!(read(&log).unwrap(), b"");
    let log1 = dir.path().join("file.log.1");
    assert_eq!(read(&log1).unwrap(), b"997\n998\n999\n1000\n");
    let log2 = dir.path().join("file.log.2");
    assert_eq!(read(&log2).unwrap(), b"993\n994\n995\n996\n");
    let log3 = dir.path().join("file.log.3");
    assert_eq!(read(&log3).unwrap(), b"989\n990\n991\n992\n");
    let log4 = dir.path().join("file.log.4");
    assert!(!log4.try_exists().unwrap());
  }
}
