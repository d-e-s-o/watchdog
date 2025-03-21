// Copyright (C) 2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

use std::os::fd::IntoRawFd as _;
use std::os::fd::RawFd;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::Ordering;

use anyhow::Context as _;
use anyhow::Result;

use libc::SIG_ERR;
use libc::SIGCHLD;
use libc::SIGINT;
use libc::SIGTERM;
use libc::c_int;
use libc::signal;
use libc::size_t;
use libc::write;

use mio::unix::pipe;

use crate::util::check;


/// The file descriptor used for signaling `SIGTERM` events.
static SIGTERM_FD: SignalFd = SignalFd::uninit();
/// The file descriptor used for signaling `SIGINT` events.
static SIGINT_FD: SignalFd = SignalFd::uninit();
/// The file descriptor used for signaling `SIGCHLD` events.
static SIGCHLD_FD: SignalFd = SignalFd::uninit();


#[derive(Debug)]
struct SignalFd {
  fd: AtomicU64,
}

impl SignalFd {
  const fn uninit() -> Self {
    Self {
      fd: AtomicU64::new(0),
    }
  }

  fn set_sender(&self, sender: pipe::Sender) {
    let fd = sender.into_raw_fd();
    assert!(
      size_of_val(&fd) <= size_of_val(&self.fd),
      "platform file descriptor does not fit into u64"
    );
    assert_ne!(fd, 0);

    let () = self.fd.store(fd as _, Ordering::SeqCst);
  }

  fn signal(&self) {
    let fd = self.fd.load(Ordering::Relaxed);
    assert_ne!(fd, 0, "SignalFd was not properly initialized");
    let fd = fd as RawFd;

    let buffer = b"\0";
    let result = unsafe { write(fd, buffer.as_ptr() as *const _, buffer.len()) };
    check(result, -1).unwrap();
  }
}


/// A signal handler for `SIGTERM`.
extern "C" fn sigterm_handler(signum: c_int) {
  debug_assert!([SIGTERM].contains(&signum));
  let () = SIGTERM_FD.signal();
}

/// Register a signal handler for `SIGTERM`.
pub(crate) fn sigterm_events() -> Result<pipe::Receiver> {
  let (sender, receiver) = pipe::new().context("failed to create pipe for SIGTERM signals")?;
  let () = SIGTERM_FD.set_sender(sender);
  let rc = unsafe { signal(SIGTERM, sigterm_handler as size_t) };
  let () = check(rc, SIG_ERR).context("failed to register SIGTERM handler")?;
  Ok(receiver)
}


/// A signal handler for `SIGINT`.
extern "C" fn sigint_handler(signum: c_int) {
  debug_assert!([SIGINT].contains(&signum));
  let () = SIGINT_FD.signal();
}

/// Register a signal handler for `SIGINT`.
pub(crate) fn sigint_events() -> Result<pipe::Receiver> {
  let (sender, receiver) = pipe::new().context("failed to create pipe for SIGINT signals")?;
  let () = SIGINT_FD.set_sender(sender);
  let rc = unsafe { signal(SIGINT, sigint_handler as size_t) };
  let () = check(rc, SIG_ERR).context("failed to register SIGINT handler")?;
  Ok(receiver)
}


/// A signal handler for `SIGCHLD`.
extern "C" fn sigchld_handler(signum: c_int) {
  debug_assert_eq!(signum, SIGCHLD);
  let () = SIGCHLD_FD.signal();
}

/// Register a signal handler for `SIGCHLD`.
pub(crate) fn sigchld_events() -> Result<pipe::Receiver> {
  let (sender, receiver) = pipe::new().context("failed to create pipe for SIGCHLD events")?;
  let () = SIGCHLD_FD.set_sender(sender);
  let rc = unsafe { signal(SIGCHLD, sigchld_handler as size_t) };
  let () = check(rc, SIG_ERR).context("failed to register SIGCHLD handler")?;
  Ok(receiver)
}
