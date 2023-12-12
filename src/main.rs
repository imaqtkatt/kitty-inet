pub mod display;
pub mod from_net;
pub mod runtime;
pub mod term;
pub mod to_net;

use std::io;

use chumsky::prelude::*;

fn main() {
  use std::io::Write;

  let mut loops = 0;

  const EXIT_CMD: fn() = || {
    println!("Goodbye!");
    std::process::exit(0);
  };
  const CLEAR_CMD: fn() = || {
    std::process::Command::new("clear").status().unwrap();
  };

  static CMDS: &[(&'static str, fn())] =
    &[(":exit", EXIT_CMD), (":clear", CLEAR_CMD)];

  'repl: loop {
    let mut line = String::new();

    let w = format!("({})> ", loops);
    io::stdout().write(w.as_bytes()).unwrap();
    io::stdout().flush().unwrap();

    io::stdin().read_line(&mut line).unwrap();
    line = String::from(line.trim());

    if let Some((_, f)) = CMDS.iter().find(|(cmd, _)| cmd == &line) {
      f();
      continue 'repl;
    }

    let res = term::parser().parse(line);

    match res {
      Ok(term) => {
        let term = term::desugar(term);
        let mut inet = term.to_net();
        println!("nodes: {:#}", &inet);
        inet.normal();
        let rewrites = inet.rewrites;
        println!("normal: {:#}", &inet);
        let term = inet.term_of();
        loops += 1;
        println!("res: {}\nrewrites: {}", term, rewrites);
      }
      Err(e) => println!("{e:?}"),
    }
  }
}
