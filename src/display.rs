use std::fmt;

use crate::{
  runtime::{Agent, INet, Port, AgentKind::{*, self}},
  term::Term,
};

impl fmt::Display for Term {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Era => write!(f, "*"),
      Self::Bol(b) => write!(f, "{b}"),
      Self::Var(name) => write!(f, "{}", name),
      Self::Num(val) => write!(f, "#{}", val),
      Self::Lam(name, body) => write!(f, "λ{name}. {body}"),
      Self::Ope(op, l, r) => write!(f, "({:?} {} {})", op, l, r),
      Self::App(func, argm) => write!(f, "({func} {argm})"),
      Self::Sup(first, second) => write!(f, "{{{first} {second}}}"),
      Self::Dup(first, second, val, next) => {
        write!(f, "dup {first} {second} = {val}; {next}")
      }
      Self::Let(bind, val, next) => {
        write!(f, "let {bind} = {val} in\n\t{next}")
      }
      Self::If(cond, r#then, r#else) => {
        write!(f, "if {cond} then {} else {}", r#then, r#else)
      }
    }
  }
}

impl fmt::Display for INet {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    writeln!(f, "[")?;
    for node in self.nodes.iter() {
      writeln!(f, "  {node}")?;
    }
    writeln!(f, "]")?;

    Ok(())
  }
}

impl fmt::Display for Agent {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "[{} {} {}]{{{}}}",
      self.main, self.aux1, self.aux2, self.kind
    )
  }
}

impl fmt::Display for Port {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({}:{})", self.0, self.1)
  }
}

impl fmt::Display for AgentKind {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Era => write!(f, "era"),
      Con => write!(f, "con"),
      Bol { val } => write!(f, "%{val}"),
      Dup { label } => write!(f, "dup({label})"),
      Num { val } => write!(f, "#{}", val),
      Op2 { kind } => write!(f, "{:?}", kind),
      Op1 { kind, val } => write!(f, "{{{:?} #{}}}", kind, val),
      Cnd => write!(f, "cond"),
    }
  }
}
