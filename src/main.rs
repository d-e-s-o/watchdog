// Copyright (C) 2018-2025 Daniel Mueller <deso@posteo.net>
// SPDX-License-Identifier: GPL-3.0-or-later

#![allow(clippy::let_and_return)]

//! A watchdog for starting and restarting another program.

mod args;
mod backoff;
mod logger;
mod rotate;
mod signal;
mod util;
mod watched;

use std::ffi::OsStr;
use std::io::ErrorKind;
use std::mem::forget;
use std::mem::replace;
use std::ops::BitOr;
use std::ops::BitOrAssign;
use std::ops::Deref as _;
use std::os::unix::process::ExitStatusExt;
use std::process::ExitStatus;
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;
use std::time::Instant;

use anyhow::Context;
use anyhow::Result;

use clap::Parser as _;

use log::debug;
use log::error;
use log::warn;

use mio::Events;
use mio::Interest;
use mio::Poll;
use mio::Token;
use mio::unix::pipe::Receiver;

use crate::args::Args;
use crate::backoff::Backoff;
use crate::logger::init_logging;
use crate::rotate::Rotate;
use crate::signal::sigchld_events;
use crate::signal::sigint_events;
use crate::signal::sigterm_events;
use crate::watched::PollData;
use crate::watched::Streams;
use crate::watched::Watched;


/// Format a command with the given list of arguments as a string.
fn format_command<C, A, S>(command: C, args: A) -> String
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  args.into_iter().fold(
    command.as_ref().to_string_lossy().into_owned(),
    |mut cmd, arg| {
      cmd += " ";
      cmd += arg.as_ref().to_string_lossy().deref();
      cmd
    },
  )
}


fn evaluate_status<C, A, S>(status: ExitStatus, command: C, args: A)
where
  C: AsRef<OsStr>,
  A: IntoIterator<Item = S>,
  S: AsRef<OsStr>,
{
  let command = format_command(command, args);
  if status.success() {
    warn!("`{command}` exited successfully");
  } else {
    let code = if let Some(code) = status.code() {
      format!(" ({code})")
    } else {
      format!(
        " (terminated by signal{})",
        status
          .signal()
          .map(|num| format!(" {num}"))
          .unwrap_or_default()
      )
    };

    error!("`{command}` reported non-zero exit-status{code}");
  }
}


fn kill_child_now(watched: Watched) -> Action {
  debug!("forcefully killing child process");
  if let Err(err) = watched.kill() {
    warn!("failed to kill child process: {err:?}");
  }
  Action::Exit
}

fn min_opt<T>(a: Option<T>, b: Option<T>) -> Option<T>
where
  T: Copy + Ord,
{
  match (a, b) {
    (Some(a), Some(b)) => Some(a.min(b)),
    (a @ Some(_), None) => a,
    (None, b @ Some(_)) => b,
    (None, None) => None,
  }
}


#[derive(Clone, Copy, Debug)]
enum Action {
  /// Exit the program altogether.
  Exit,
  /// Re-invoke our event loop with the provided timeout.
  Poll(Option<Duration>),
}

impl BitOr for Action {
  type Output = Action;

  #[inline]
  fn bitor(self, other: Self) -> Self::Output {
    let mut result = self;
    result |= other;
    result
  }
}

impl BitOrAssign for Action {
  #[inline]
  fn bitor_assign(&mut self, other: Self) {
    match (*self, other) {
      (Self::Exit, _) => (),
      (_, Self::Exit) => *self = Self::Exit,
      (Self::Poll(timeout_slf), Self::Poll(timeout_other)) => {
        *self = Self::Poll(min_opt(timeout_slf, timeout_other))
      },
    }
  }
}


#[derive(Debug)]
struct Running {
  spawned: Instant,
  watched: Watched,
}

#[derive(Debug)]
struct Signaled {
  watched: Watched,
  kill_at: Option<Instant>,
}

#[derive(Debug)]
struct BackingOff {
  until: Instant,
}

#[derive(Debug)]
enum State {
  Running(Running),
  Signaled(Signaled),
  BackingOff(BackingOff),
  Undefined,
}

impl State {
  fn into_running(self) -> Option<Running> {
    match self {
      State::Running(running) => Some(running),
      _ => None,
    }
  }

  fn into_signaled(self) -> Option<Signaled> {
    match self {
      State::Signaled(signaled) => Some(signaled),
      _ => None,
    }
  }
}


struct Watchdog<'args> {
  args: &'args Args,
  backoff: &'args mut Backoff,
  state: State,
  rotate: Option<Arc<Mutex<Rotate>>>,
}

impl<'args> Watchdog<'args> {
  fn start(
    args: &'args Args,
    backoff: &'args mut Backoff,
    rotate: Option<Arc<Mutex<Rotate>>>,
  ) -> Result<Self> {
    let slf = Self {
      args,
      backoff,
      state: State::Running(Self::launch(args)?),
      rotate,
    };
    Ok(slf)
  }

  /// Restart the watched process.
  fn restart(&mut self, now: Instant) -> Action {
    match Self::launch(self.args) {
      Ok(running) => {
        self.state = State::Running(running);
        Action::Poll(None)
      },
      Err(err) => {
        error!("failed to restart child: {err:#}");
        self.try_restart(now, now)
      },
    }
  }

  /// Try restarting the watched process, unless we should back off
  /// first.
  fn try_restart(&mut self, spawned: Instant, now: Instant) -> Action {
    let delay = self.backoff.next_delay(spawned, now);
    if let Some(delay_) = delay {
      debug!("using back off delay {:?}", delay_);
      self.state = State::BackingOff(BackingOff {
        until: now + delay_,
      });
      Action::Poll(delay)
    } else {
      self.restart(now)
    }
  }

  fn launch(args: &Args) -> Result<Running> {
    let formatted = format_command(&args.command, &args.arguments);
    debug!("starting process `{formatted}`");

    let spawned = Instant::now();
    let watched = Watched::builder()
      .set_log_streams(
        args
          .log_file
          .as_ref()
          .map(|_| args.log_streams.unwrap_or(Streams::Both)),
      )
      .build(&args.command, &args.arguments)
      .with_context(|| format!("failed to execute `{formatted}`"))?;
    let running = Running { spawned, watched };
    Ok(running)
  }

  fn on_sigterm(&mut self) -> Action {
    match &mut self.state {
      State::Running(_) => {
        let timeout = Duration::from_millis(500);
        // SANITY: We know that our state is `Running`.
        let running = replace(&mut self.state, State::Undefined)
          .into_running()
          .unwrap();
        let signaled = Signaled {
          watched: running.watched,
          kill_at: Some(Instant::now() + timeout),
        };
        self.state = State::Signaled(signaled);
        Action::Poll(Some(timeout))
      },
      State::Signaled(_) => {
        // We got signaled a second time. Fast track the killing of the
        // watched process.
        // SANITY: We know that our state is `Signaled`.
        let signaled = replace(&mut self.state, State::Undefined)
          .into_signaled()
          .unwrap();
        kill_child_now(signaled.watched)
      },
      State::BackingOff(..) => Action::Exit,
      State::Undefined => unreachable!(),
    }
  }

  fn on_sigint(&mut self) -> Action {
    match &mut self.state {
      State::Running(running) => {
        match running.watched.terminate() {
          Ok(()) => {
            // SANITY: We know that our state is `Running`.
            let running = replace(&mut self.state, State::Undefined)
              .into_running()
              .unwrap();
            let signaled = Signaled {
              watched: running.watched,
              kill_at: None,
            };
            self.state = State::Signaled(signaled);
            return Action::Poll(None)
          },
          Err(err) => {
            warn!("failed to terminate child process gracefully: {err:#}");
          },
        }

        // SANITY: We know that our state is `Running`.
        let running = replace(&mut self.state, State::Undefined)
          .into_running()
          .unwrap();
        kill_child_now(running.watched)
      },
      State::Signaled(_) => {
        // SANITY: We know that our state is `Signaled`.
        let signaled = replace(&mut self.state, State::Undefined)
          .into_signaled()
          .unwrap();
        kill_child_now(signaled.watched)
      },
      State::BackingOff(..) => Action::Exit,
      State::Undefined => unreachable!(),
    }
  }

  fn on_sigchld(&mut self) -> Action {
    match &mut self.state {
      State::Running(running) => {
        match running.watched.try_wait() {
          Ok(Some(status)) => {
            let () = evaluate_status(status, &self.args.command, &self.args.arguments);
            let spawned = running.spawned;
            self.try_restart(spawned, Instant::now())
          },
          Ok(None) => {
            // This state can only be interpreted as a spurious wake up.
            // So just continue whatever it was that we were doing.
            Action::Poll(None)
          },
          Err(err) => {
            // There aren't really any error conditions that `waitpid`
            // reports that we may be able to recover from or have an
            // idea what to do about other than restart the child.
            // `ECHILD` would indicate a death of the child that got
            // unnoticed, so restarting is the right call. Other cases
            // likely indicate wrong inputs, which should not ever
            // occur. In an attempt to give us the highest chance of
            // recovery, restart there as well.
            warn!("failed to await child: {err:#}");
            let spawned = running.spawned;
            self.try_restart(spawned, Instant::now())
          },
        }
      },
      State::Signaled(signaled) => {
        match signaled.watched.try_wait() {
          Ok(Some(status)) => {
            let () = evaluate_status(status, &self.args.command, &self.args.arguments);
            Action::Exit
          },
          Ok(None) => {
            // If we reached `kill_at` we schedule another poll with a
            // timeout of 0, which should fire immediately.
            let remaining = signaled
              .kill_at
              .map(|kill_at| kill_at.saturating_duration_since(Instant::now()));
            Action::Poll(remaining)
          },
          Err(err) => {
            warn!("failed to await child: {err:#}");
            // SANITY: We know that our state is `Signaled`.
            let signaled = replace(&mut self.state, State::Undefined)
              .into_signaled()
              .unwrap();
            kill_child_now(signaled.watched)
          },
        }
      },
      State::BackingOff(backing_off) => {
        // We should never receive a signal pertaining a child when no
        // child is running. So basically just continue the backoff.
        let remaining = backing_off.until.saturating_duration_since(Instant::now());
        Action::Poll(Some(remaining))
      },
      State::Undefined => unreachable!(),
    }
  }

  fn on_timeout(&mut self) -> Action {
    match &mut self.state {
      State::Running(_) => {
        // This likely was a spurious wake up of sorts.
        Action::Poll(None)
      },
      State::Signaled(_) => {
        // Strictly speaking we should probably check `kill_at` to
        // handle spurious wake ups of sorts gracefully. But let's not
        // complicate this path unnecessarily given that the eventual
        // outcome is the same.
        // SANITY: We know that our state is `Signaled`.
        let signaled = replace(&mut self.state, State::Undefined)
          .into_signaled()
          .unwrap();
        kill_child_now(signaled.watched)
      },
      State::BackingOff(backing_off) => {
        let now = Instant::now();
        let remaining = backing_off.until.checked_duration_since(now);

        if remaining.is_some() {
          Action::Poll(remaining)
        } else {
          // The backoff expired. Restart the process.
          self.restart(now)
        }
      },
      State::Undefined => unreachable!(),
    }
  }

  fn on_stream_ready(&mut self, stream: &mut Receiver) {
    if let Some(rotate) = &mut self.rotate {
      let result = rotate
        .lock()
        .unwrap_or_else(|err| err.into_inner())
        .forward(stream);
      if let Err(err) = result {
        warn!("failed to forward stdio stream output: {err:#}");
      }
    } else {
      debug_assert!(
        false,
        "encountered stream ready event when no streams should be forwarded"
      );
    }
  }

  fn take_poll_data(&mut self) -> Option<PollData> {
    match &mut self.state {
      State::Running(Running { watched, .. }) | State::Signaled(Signaled { watched, .. }) => {
        watched.take_poll_data()
      },
      State::BackingOff(_) => None,
      State::Undefined => unreachable!(),
    }
  }
}


fn run(mut watchdog: Watchdog<'_>) {
  let mut poll = Poll::new().expect("failed to create poll instance");
  let mut events = Events::with_capacity(16);

  let mut sigterm_events = sigterm_events().expect("failed to register SIGTERM handler");
  let sigterm_token = Token(0);
  let mut sigint_events = sigint_events().expect("failed to register SIGINT handler");
  let sigint_token = Token(1);
  let mut sigchld_events = sigchld_events().expect("failed to register SIGCHLD handler");
  let sigchld_token = Token(2);

  let () = poll
    .registry()
    .register(&mut sigterm_events, sigterm_token, Interest::READABLE)
    .expect("failed to register poll for SIGTERM events");
  let () = poll
    .registry()
    .register(&mut sigint_events, sigint_token, Interest::READABLE)
    .expect("failed to register poll for SIGINT events");
  let () = poll
    .registry()
    .register(&mut sigchld_events, sigchld_token, Interest::READABLE)
    .expect("failed to register poll for SIGCHLD events");

  // Forget our fixed pipe read ends here so that they won't get
  // dropped. If we exit below loop we are going to terminate anyway,
  // and we do not want the write ends to potentially panic in a signal
  // handler.
  forget(sigterm_events);
  forget(sigint_events);
  forget(sigchld_events);

  let mut stdout_token = Token(3);
  let mut stderr_token = Token(4);
  let mut next_token = 5;
  let mut poll_data = Option::<PollData>::None;

  let mut timeout = None;
  loop {
    if let Some(mut new_poll_data) = watchdog.take_poll_data() {
      if let Some(mut poll_data) = poll_data {
        if let Some(stdout) = &mut poll_data.stdout {
          let _result = poll.registry().deregister(stdout);
        }

        if let Some(stderr) = &mut poll_data.stderr {
          let _result = poll.registry().deregister(stderr);
        }
      }

      // We always make sure to create a new token as a safety
      // precaution
      stdout_token = Token(next_token);
      // TODO: Strictly speaking we should use wrapping arithmetic here,
      //       but then we'd also need to make sure to never include the
      //       fixed first three tokens.
      next_token += 1;
      stderr_token = Token(next_token);
      next_token += 1;

      if let Some(stdout) = &mut new_poll_data.stdout {
        let () = poll
          .registry()
          .register(stdout, stdout_token, Interest::READABLE)
          .expect("failed to register poll for stdout");
      }
      if let Some(stderr) = &mut new_poll_data.stderr {
        let () = poll
          .registry()
          .register(stderr, stderr_token, Interest::READABLE)
          .expect("failed to register poll for stderr");
      }
      poll_data = Some(new_poll_data);
    }

    match poll.poll(&mut events, timeout) {
      Ok(()) => {
        let mut action = Action::Poll(None);
        for event in events.iter() {
          match event.token() {
            token if token == sigterm_token => {
              action |= watchdog.on_sigterm();
            },
            token if token == sigint_token => {
              action |= watchdog.on_sigint();
            },
            token if token == sigchld_token => {
              action |= watchdog.on_sigchld();
            },
            token if token == stdout_token => {
              if let Some(stdout) = poll_data.as_mut().and_then(|data| data.stdout.as_mut()) {
                let () = watchdog.on_stream_ready(stdout);
              }
            },
            token if token == stderr_token => {
              if let Some(stderr) = poll_data.as_mut().and_then(|data| data.stderr.as_mut()) {
                let () = watchdog.on_stream_ready(stderr);
              }
            },
            token => debug!("received event on unexpected token: {token:?}"),
          }
        }

        if events.is_empty() {
          action |= watchdog.on_timeout();
        }

        match action {
          Action::Poll(new_timeout) => timeout = new_timeout,
          Action::Exit => return,
        }
      },
      Err(err) if err.kind() == ErrorKind::Interrupted => continue,
      Err(err) => {
        // SANITY: We should not hit this case, as the remaining
        //         conditions for the underlying epoll_wait system
        //         call to fail are all related to faulty inputs.
        Err(err).context("failed to poll events").unwrap()
      },
    }
  }
}

fn main() -> Result<()> {
  let args = Args::parse();
  let rotate = if let Some(log_file) = &args.log_file {
    let rotate = Rotate::builder()
      .set_max_lines(args.max_log_lines)
      .set_max_files(args.max_log_files)
      .build(log_file)?;
    Some(Arc::new(Mutex::new(rotate)))
  } else {
    None
  };
  let () = init_logging(args.verbosity, rotate.as_ref().map(Arc::clone));
  let mut backoff = Backoff::new(args.backoff_base, args.backoff_multiplier, args.backoff_max);
  let watchdog = Watchdog::start(&args, &mut backoff, rotate)?;

  let () = run(watchdog);
  Ok(())
}
