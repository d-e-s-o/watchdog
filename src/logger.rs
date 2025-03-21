// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::io;
use std::io::Write as _;
use std::io::stderr;
use std::mem::MaybeUninit;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::SystemTime;

use anyhow::Result;

use bufio::Writer as StackWriter;

use log::Level;
use log::Log;
use log::Metadata;
use log::Record;
use log::max_level;
use log::set_logger;
use log::set_max_level;

use jiff::Timestamp;

use crate::rotate::Rotate;

const RESET: &str = "\x1b[0m";
const GREEN_S: &str = "\x1b[32m";
const GREEN_E: &str = RESET;
const BLUE_S: &str = "\x1b[34m";
const BLUE_E: &str = RESET;
const RED_S: &str = "\x1b[31m";
const RED_E: &str = RESET;
const YELLOW_S: &str = "\x1b[33m";
const YELLOW_E: &str = RESET;
const MAGENTA_S: &str = "\x1b[35m";
const MAGENTA_E: &str = RESET;


// A replacement of the standard write!() macro that silently ignores
// short writes.
macro_rules! write {
  ($($arg:tt)*) => {
    match std::write!($($arg)*) {
      Err(err) if err.kind() == io::ErrorKind::WriteZero => Ok(()),
      result => result,
    }
  };
}


#[derive(Debug)]
struct Logger {
  // TODO: It is extremely unfortunately that `log::Log` requires us to
  //       be `Send` + `Sync`. We could consider rolling our own logging
  //       infrastructure to make do with lighter weight mechanisms for
  //       sharing.
  rotate: Option<Arc<Mutex<Rotate>>>,
}

impl Log for Logger {
  fn enabled(&self, metadata: &Metadata) -> bool {
    metadata.level() <= max_level()
  }

  fn log(&self, record: &Record) {
    fn log_impl(logger: &Logger, record: &Record) -> Result<()> {
      // We effectively buffer every log line here while capping line
      // length at a fixed upper limit. In many ways that just simulates
      // a `BufReader`, but we don't heap allocate. Buffering is useful,
      // because it means we minimize the performance penalty for
      // writes to unbuffered stderr.
      let mut buffer = [MaybeUninit::<u8>::uninit(); 256];
      let mut writer = StackWriter::new(&mut buffer);

      let time = Timestamp::try_from(SystemTime::now())
        .map_err(|err| io::Error::new(io::ErrorKind::Other, err))?;
      let () = write!(&mut writer, "[{time:.3} ")?;

      let () = match record.level() {
        Level::Trace => write!(&mut writer, "{MAGENTA_S}TRACE{MAGENTA_E}"),
        Level::Debug => write!(&mut writer, " {BLUE_S}INFO{BLUE_E}"),
        Level::Info => write!(&mut writer, " {GREEN_S}INFO{GREEN_E}"),
        Level::Warn => write!(&mut writer, " {YELLOW_S}WARN{YELLOW_E}"),
        Level::Error => write!(&mut writer, "{RED_S}ERROR{RED_E}"),
      }?;

      let () = write!(&mut writer, " {}] {}", record.target(), record.args())?;

      if let Some(rotate) = &logger.rotate {
        let mut rotate = rotate.lock().unwrap_or_else(|err| err.into_inner());
        let () = rotate.forward(&mut writer.written())?;
        let () = rotate.forward(&mut b"\n".as_slice())?;
      } else {
        let mut stderr = stderr().lock();
        let () = stderr.write_all(writer.written())?;
        // We exclude the newline from the write! machinery and have it
        // here unconditionally just in case we experience short writes
        // due to our limited size buffer.
        let () = stderr.write_all(b"\n")?;
      }
      Ok(())
    }

    #[allow(clippy::collapsible_if)]
    if self.enabled(record.metadata()) {
      if let Err(err) = log_impl(self, record) {
        eprintln!("failed to format and/or write log line: {err}")
      }
    }
  }

  fn flush(&self) {}
}


/// Initialize the logging subsystem with the given abstract notion of
/// verbosity (higher values equate to higher verbosity).
pub(crate) fn init_logging(verbosity: u8, rotate: Option<Arc<Mutex<Rotate>>>) {
  let level = match verbosity {
    0 => Level::Warn,
    1 => Level::Info,
    2 => Level::Debug,
    _ => Level::Trace,
  };

  let () = set_max_level(level.to_level_filter());
  let logger = Logger { rotate };
  let () = set_logger(Box::leak(Box::new(logger))).expect("failed to register logger");
}


#[cfg(test)]
mod tests {
  use super::*;


  /// Check that our `write!` macro replacement works as it should.
  #[test]
  fn exceeding_write() {
    let mut buffer = [0u8; 17];
    let mut cursor = &mut buffer[0..16];

    let () = write!(cursor, "foobarbazislongerthansixteencharacters").unwrap();
    assert_eq!(buffer.as_slice(), b"foobarbazislonge\0");
  }
}
