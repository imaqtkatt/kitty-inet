use chumsky::prelude::*;

use crate::runtime::OpKind;

#[derive(Clone)]
pub enum Term {
  Era,
  Bol(bool),
  Var(String),
  Num(isize),
  Lam(String, Box<Term>),
  Ope(OpKind, Box<Term>, Box<Term>),
  App(Box<Term>, Box<Term>),
  Sup(Box<Term>, Box<Term>),
  Dup(String, String, Box<Term>, Box<Term>),
  Let(String, Box<Term>, Box<Term>),
  If(Box<Term>, Box<Term>, Box<Term>),
}

pub fn parser() -> impl Parser<char, Term, Error = Simple<char>> {
  let ident = text::ident().padded();

  recursive(|term| {
    let era = just('(').ignore_then(just(')')).to(Term::Era);

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

    let r#if = text::keyword("if")
      .ignore_then(term.clone().padded())
      .then_ignore(text::keyword("then"))
      .then(term.clone().padded())
      .then_ignore(text::keyword("else"))
      .then(term.clone().padded())
      .map(|((cond, r#then), r#else)| {
        Term::If(Box::new(cond), Box::new(r#then), Box::new(r#else))
      })
      .boxed();

    let r#let = text::keyword("let")
      .ignore_then(ident)
      .then_ignore(just('='))
      .then(term.clone().padded())
      .then_ignore(text::keyword("in"))
      .then(term.clone().padded())
      .map(|((bind, val), next)| Term::Let(bind, Box::new(val), Box::new(next)))
      .boxed();

    let r#true = text::keyword("true").to(Term::Bol(true)).boxed();
    let r#false = text::keyword("false").to(Term::Bol(false)).boxed();

    let delimited = term.clone().delimited_by(just('('), just(')'));

    choice((
      r#true, r#false, r#let, app, sup, dup, r#if, lam, op2, op1, var, num,
      era, delimited,
    ))
  })
}

pub fn desugar(term: Term) -> Term {
  match term {
    Term::Let(bind, val, next) => {
      let lam = Term::Lam(bind, next);
      Term::App(Box::new(lam), val)
    }
    _ => term,
  }
}
