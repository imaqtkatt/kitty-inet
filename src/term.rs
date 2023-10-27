use chumsky::prelude::*;
use std::fmt;

use crate::{INet, OpKind, ROOT};

#[derive(Clone)]
pub enum Term {
  Era,
  Var(String),
  Num(isize),
  Lam(String, Box<Term>),
  Ope(OpKind, Box<Term>, Box<Term>),
  App(Box<Term>, Box<Term>),
  Sup(Box<Term>, Box<Term>),
  Dup(String, String, Box<Term>, Box<Term>),
}

impl Term {
  pub fn to_net(&self) -> INet {
    let mut inet = INet::default();
    inet.inject(self, ROOT);
    inet
  }
}

pub fn parser() -> impl Parser<char, Term, Error = Simple<char>> {
  let ident = text::ident().padded();

  recursive(|term| {
    let era = just('\'').to(Term::Era);

    let var = ident.map(|s| Term::Var(s)).boxed();

    let num = text::digits(10)
      .padded()
      .map(|n: String| Term::Num(n.parse().unwrap()))
      .boxed();

    let lam = just('@')
      .ignore_then(ident)
      .then(term.clone().padded())
      .map(|(name, body)| Term::Lam(name, Box::new(body)))
      .boxed();

    let add = just('+').to(OpKind::Add);
    let sub = just('-').to(OpKind::Sub);
    let mul = just('*').to(OpKind::Mul);
    let div = just('/').to(OpKind::Div);
    let shl = just('<').ignore_then(just('<')).to(OpKind::Shl);
    let shr = just('>').ignore_then(just('>')).to(OpKind::Shr);
    let eql = just('=').ignore_then(just('=')).to(OpKind::Eql);
    let neq = just('!').ignore_then(just('=')).to(OpKind::Neq);
    let ops = choice((add, sub, mul, div, shl, shr, eql, neq));

    let not = just('~').to(OpKind::Not);
    let op1 = not
      .then(term.clone().padded())
      .delimited_by(just('('), just(')'))
      .map(|(kind, t)| {
        Term::Ope(kind, Box::new(Term::Num(isize::MIN)), Box::new(t))
      })
      .boxed();

    let op2 = ops
      .then(term.clone().padded())
      .then(term.clone().padded())
      .delimited_by(just('('), just(')'))
      .map(|((op, l), r)| Term::Ope(op, Box::new(l), Box::new(r)))
      .boxed();

    let app = term
      .clone()
      .then(term.clone().padded().repeated())
      .foldl(|x, y| Term::App(Box::new(x), Box::new(y)))
      .delimited_by(just('(').padded(), just(')').padded())
      .boxed();

    let sup = term
      .clone()
      .padded()
      .then(term.clone().padded())
      .delimited_by(just('{'), just('}'))
      .map(|(first, second)| Term::Sup(Box::new(first), Box::new(second)))
      .boxed();

    let dup = text::keyword("dup")
      .ignore_then(ident)
      .then(ident)
      .then_ignore(just('='))
      .then(term.clone().padded())
      .then_ignore(just(';'))
      .then(term.clone().padded())
      .map(|(((first, second), val), next)| {
        Term::Dup(first, second, Box::new(val), Box::new(next))
      })
      .boxed();

    let idk = term.clone().delimited_by(just('('), just(')'));

    choice((app, sup, dup, lam, op2, op1, var, num, era, idk))
  })
}

impl fmt::Display for Term {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Era => write!(f, "*"),
      Self::Var(name) => write!(f, "{}", name),
      Self::Num(val) => write!(f, "#{}", val),
      Self::Lam(name, body) => write!(f, "λ{name}. {body}"),
      Self::Ope(op, l, r) => write!(f, "({:?} {} {})", op, l, r),
      Self::App(func, argm) => write!(f, "({func} {argm})"),
      Self::Sup(first, second) => write!(f, "{{{first} {second}}}"),
      Self::Dup(first, second, val, next) => {
        write!(f, "dup {first} {second} = {val}; {next}")
      }
    }
  }
}
