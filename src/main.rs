use std::{
  collections::{HashMap, HashSet},
  fmt,
  hash::Hash,
};

use chumsky::prelude::*;
use AgentKind::*;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AgentKind {
  Era = 0,
  Con,
  Dup,
}

impl fmt::Display for AgentKind {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Era => write!(f, "era"),
      Con => write!(f, "con"),
      Dup => write!(f, "dup"),
    }
  }
}

type AgentId = u8;
type SlotId = u8;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Port(pub AgentId, pub SlotId);

const ROOT: Port = Port(0, 1);

impl Port {
  pub fn agent(self) -> AgentId {
    self.0
  }

  pub fn slot(self) -> SlotId {
    self.1
  }

  pub fn is_main(self) -> bool {
    self.1 == 0
  }

  pub fn main(id: AgentId) -> Self {
    Port(id, 0)
  }

  pub fn aux1(id: AgentId) -> Self {
    Port(id, 1)
  }

  pub fn aux2(id: AgentId) -> Self {
    Port(id, 2)
  }
}

impl fmt::Display for Port {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "({}, {})", self.0, self.1)
  }
}

#[derive(Clone, Copy)]
pub struct Agent {
  pub main: Port,
  pub aux1: Port,
  pub aux2: Port,
  pub kind: AgentKind,
}

impl fmt::Display for Agent {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "[{} {} {} {}]",
      self.main, self.aux1, self.aux2, self.kind
    )
  }
}

impl fmt::Debug for Agent {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "[{} {} {} {}]",
      self.main, self.aux1, self.aux2, self.kind
    )
  }
}

impl Agent {
  pub fn new(main: Port, aux1: Port, aux2: Port, kind: AgentKind) -> Self {
    Self {
      main,
      aux1,
      aux2,
      kind,
    }
  }

  pub fn with_id(id: AgentId, kind: AgentKind) -> Self {
    Self {
      main: Port(id, 0),
      aux1: Port(id, 1),
      aux2: Port(id, 2),
      kind,
    }
  }

  pub fn port(&self, slot: SlotId) -> Port {
    match slot {
      0 => self.main,
      1 => self.aux1,
      2 => self.aux2,
      _ => unreachable!(),
    }
  }

  pub fn port_mut(&mut self, slot: SlotId) -> &mut Port {
    match slot {
      0 => &mut self.main,
      1 => &mut self.aux1,
      2 => &mut self.aux2,
      _ => unreachable!(),
    }
  }
}

pub struct INet {
  pub nodes: Vec<Agent>,
  pub free: Vec<AgentId>,
}

impl Default for INet {
  fn default() -> Self {
    Self {
      nodes: vec![Agent::new(Port(0, 2), Port(0, 1), Port(0, 0), Era)],
      free: Default::default(),
    }
  }
}

impl INet {
  #[inline(always)]
  pub fn new_id(&mut self) -> AgentId {
    self.free.pop().unwrap_or(self.nodes.len() as AgentId)
  }

  #[inline(always)]
  pub fn alloc(&mut self, kind: AgentKind) -> AgentId {
    let id = self.new_id();
    self.nodes[id as usize] = Agent::with_id(id, kind);
    id
  }

  #[inline(always)]
  pub fn free(&mut self, id: AgentId) {
    self.free.push(id)
  }

  #[inline(always)]
  pub fn link(&mut self, a: Port, b: Port) {
    *self.nodes[a.agent() as usize].port_mut(a.slot()) = b;
    *self.nodes[b.agent() as usize].port_mut(b.slot()) = a;
  }

  #[inline(always)]
  pub fn enter(&mut self, port: Port) -> Port {
    self.nodes[port.agent() as usize].port(port.slot())
  }

  #[inline(always)]
  pub fn agent_kind(&self, id: AgentId) -> AgentKind {
    self.nodes[id as usize].kind
  }

  #[inline(always)]
  pub fn rewrite(&mut self, a: AgentId, b: AgentId) {
    let a_kind = self.agent_kind(a);
    let b_kind = self.agent_kind(b);

    if a_kind == b_kind {
      self.comm(a, b);
    } else {
      self.anni(a_kind, b_kind, a, b);
    }
  }

  #[inline(always)]
  fn comm(&mut self, a: AgentId, b: AgentId) {
    let a_aux = self.enter(Port(a, 1));
    let b_aux = self.enter(Port(b, 1));
    self.link(a_aux, b_aux);
    let a_aux = self.enter(Port(a, 2));
    let b_aux = self.enter(Port(b, 2));
    self.link(a_aux, b_aux);

    self.free.push(a);
    self.free.push(b);
  }

  #[inline(always)]
  fn anni(
    &mut self,
    a_kind: AgentKind,
    b_kind: AgentKind,
    a: AgentId,
    b: AgentId,
  ) {
    let a_new = self.alloc(a_kind);
    let b_new = self.alloc(b_kind);

    let aux = self.enter(Port(a, 1));
    self.link(Port(b_new, 0), aux);
    let aux = self.enter(Port(a, 2));
    self.link(Port(b, 0), aux);
    let aux = self.enter(Port(b, 1));
    self.link(Port(a_new, 0), aux);
    let aux = self.enter(Port(b, 2));
    self.link(Port(a, 0), aux);

    self.link(Port(a_new, 1), Port(b_new, 1));
    self.link(Port(a_new, 2), Port(b, 1));
    self.link(Port(a, 1), Port(b_new, 2));
    self.link(Port(a, 2), Port(b, 2))
  }

  pub fn reduce(&mut self, root: Port) {
    let mut path = Vec::new();
    let mut prev = root;

    loop {
      let next = self.enter(prev);

      if next == ROOT {
        return;
      }

      if next.is_main() {
        if prev.is_main() {
          self.rewrite(prev.agent(), next.agent());
          prev = path.pop().unwrap();
          continue;
        } else {
          return;
        }
      }

      path.push(prev);
      prev = Port::main(next.agent());
    }
  }

  pub fn normal(&mut self) {
    let mut warp = vec![ROOT];

    while let Some(prev) = warp.pop() {
      self.reduce(prev);
      let next = self.enter(prev);
      if next.is_main() {
        warp.push(Port(next.agent(), 1));
        warp.push(Port(next.agent(), 2));
      }
    }
  }
}

#[derive(Clone)]
pub enum Term {
  Era,
  Var(String),
  Lam(String, Box<Term>),
  App(Box<Term>, Box<Term>),
  Sup(Box<Term>, Box<Term>),
  Dup(String, String, Box<Term>, Box<Term>),
}

impl fmt::Display for Term {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Era => write!(f, "*"),
      Self::Var(name) => write!(f, "{}", name),
      Self::Lam(name, body) => write!(f, "λ{name}. {body}"),
      Self::App(func, argm) => write!(f, "({func} {argm})"),
      Self::Sup(first, second) => write!(f, "{{{first} {second}}}"),
      Self::Dup(first, second, val, next) => {
        write!(f, "dup {first} {second} = {val}; {next}")
      }
    }
  }
}

impl INet {
  pub fn term_of(&mut self) -> Term {
    self.readback(ROOT)
  }

  fn readback(&mut self, host: Port) -> Term {
    fn name_of(
      inet: &INet,
      var_port: Port,
      var_name: &mut HashMap<Port, String>,
    ) -> String {
      if inet.agent_kind(var_port.agent()) == Era {
        return String::from("*");
      }

      if !var_name.contains_key(&var_port) {
        let name = index_to_name(var_name.len() as u32 + 1);
        var_name.insert(var_port, name.clone());
      }

      var_name.get(&var_port).cloned().unwrap()
    }

    fn reader(
      inet: &mut INet,
      next: Port,
      var_name: &mut HashMap<Port, String>,
      dups_vec: &mut Vec<Port>,
      dups_set: &mut HashSet<Port>,
      seen: &mut HashSet<Port>,
    ) -> Term {
      if seen.contains(&next) {
        return Term::Var(String::from("..."));
      }

      seen.insert(next);

      match inet.agent_kind(next.agent()) {
        Era => Term::Era,
        Con => match next.slot() {
          0 => {
            let name = name_of(inet, Port(next.agent(), 1), var_name);
            let port = inet.enter(Port(next.agent(), 2));
            let body = reader(inet, port, var_name, dups_vec, dups_set, seen);
            let _ = inet.enter(Port(next.agent(), 1));
            Term::Lam(name, Box::new(body))
          }
          1 => Term::Var(name_of(inet, next, var_name)),
          _ => {
            let port = inet.enter(Port::main(next.agent()));
            let func = reader(inet, port, var_name, dups_vec, dups_set, seen);
            let port = inet.enter(Port(next.agent(), 1));
            let argm = reader(inet, port, var_name, dups_vec, dups_set, seen);
            Term::App(Box::new(func), Box::new(argm))
          }
        },
        Dup => match next.slot() {
          0 => {
            let port = inet.enter(Port::aux1(next.agent()));
            let first = reader(inet, port, var_name, dups_vec, dups_set, seen);
            let port = inet.enter(Port::aux2(next.agent()));
            let second = reader(inet, port, var_name, dups_vec, dups_set, seen);
            Term::Sup(Box::new(first), Box::new(second))
          }
          _ => {
            if !dups_set.contains(&next) {
              dups_set.insert(next);
              dups_vec.push(next);
            }
            Term::Var(name_of(inet, next, var_name))
          }
        },
      }
    }

    let mut binder_name = HashMap::new();
    let mut dups_vec = Vec::new();
    let mut dups_set = HashSet::new();
    let mut seen = HashSet::new();

    let host = self.enter(host);
    let mut main = reader(
      self,
      host,
      &mut binder_name,
      &mut dups_vec,
      &mut dups_set,
      &mut seen,
    );

    while dups_vec.len() > 0 {
      let dup = dups_vec.pop().unwrap();
      let val = reader(
        self,
        dup,
        &mut binder_name,
        &mut dups_vec,
        &mut dups_set,
        &mut seen,
      );

      let first = name_of(self, Port(dup.agent(), 1), &mut binder_name);
      let second = name_of(self, Port(dup.agent(), 2), &mut binder_name);

      main = Term::Dup(first, second, Box::new(val), Box::new(main));
    }

    main
  }
}

pub fn index_to_name(idx: u32) -> String {
  let mut name = String::new();
  let mut idx = idx;
  while idx > 0 {
    idx = idx - 1;
    name.push(char::from_u32(97 + idx % 26).unwrap());
    idx = idx / 26;
  }
  return name;
}

fn parser() -> impl Parser<char, Term, Error = Simple<char>> {
  let ident = text::ident().padded();

  recursive(|term| {
    let era = just('*').to(Term::Era);

    let var = ident.map(|s| Term::Var(s)).boxed();

    let lam = just('@')
      .ignore_then(ident)
      .then(term.clone().padded())
      .map(|(name, body)| Term::Lam(name, Box::new(body)))
      .boxed();

    let app = term
      .clone()
      .then(term.clone().repeated())
      .foldl(|x, y| Term::App(Box::new(x), Box::new(y)))
      .delimited_by(just('('), just(')'))
      .boxed();

    let sup = term
      .clone()
      .then(term.clone())
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

    choice((app, sup, dup, lam, var, era))
  })
}

fn main() {
  let res = parser().parse(r"@f @x dup a b = f; (a (b x))");
  match res {
    Ok(term) => println!("{term}"),
    Err(e) => println!("wtf? {e:?}"),
  }

  let mut inet = INet::default();

  inet.nodes = vec![
    Agent::new(Port(0, 2), Port(0, 1), Port(0, 0), Con),
    Agent::new(Port(0, 0), Port(0, 0), Port(0, 0), Con),
    Agent::new(Port(0, 0), Port(0, 0), Port(0, 0), Con),
    Agent::new(Port(0, 0), Port(0, 0), Port(0, 0), Con),
  ];

  inet.link(Port::aux1(0), Port::aux2(1));
  inet.link(Port::aux1(1), Port::aux1(2));
  inet.link(Port::aux2(2), Port::main(3));
  inet.link(Port::aux1(3), Port::aux2(3));
  inet.link(Port::main(1), Port::main(2));

  inet.normal();
  println!("{}", inet.term_of());
}
