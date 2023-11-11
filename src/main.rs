#![allow(unused)]
pub mod from_net;
pub mod runtime;
pub mod term;
pub mod to_net;

use std::{
  collections::{HashMap, HashSet},
  fmt,
  hash::Hash,
  io,
};

use chumsky::prelude::*;
use runtime::{AgentKind::*, INet, Port, ROOT};
use term::Term;

fn main() {
  use std::io::Write;

  let mut loops = 0;

  loop {
    let mut line = String::new();

    let w = format!("({})> ", loops);
    io::stdout().write(w.as_bytes());
    io::stdout().flush();

    io::stdin().read_line(&mut line).unwrap();
    line = String::from(line.trim());

    match line.as_str() {
      ".exit" => {
        println!("Goodbye!");
        std::process::exit(0)
      }
      _ => {}
    }

    let res = term::parser().parse(line);

    match res {
      Ok(term) => {
        let term = term::desugar(term);
        let mut inet = term.to_net();
        println!("nodes: {:#?}\n", &inet.nodes);
        inet.normal();
        let rewrites = inet.rewrites;
        println!("normal: {:#?}\n", &inet.nodes);
        let term = inet.term_of();
        loops += 1;
        println!("res: {}\nrewrites: {}", term, rewrites);
      }
      Err(e) => println!("{e:?}"),
    }
  }
}
