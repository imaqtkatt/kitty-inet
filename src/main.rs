#![allow(unused)]
use std::{
  collections::{HashMap, HashSet},
  fmt,
  hash::Hash,
  io,
};

use chumsky::prelude::*;
use AgentKind::*;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AgentKind {
  Era = 0,
  Con,
  Dup { label: u8 },
  Num { val: isize },
  Op2 { kind: OpKind },
  Op1 { kind: OpKind, val: isize },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum OpKind {
  Add,
  Sub,
  Mul,
  Div,
  Shl,
  Shr,
  Not,
  Eql,
  Neq,
}

impl fmt::Display for AgentKind {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Era => write!(f, "era"),
      Con => write!(f, "con"),
      Dup { label } => write!(f, "dup({label})"),
      Num { val } => write!(f, "#{}", val),
      Op2 { kind } => write!(f, "{:?}", kind),
      Op1 { kind, val } => write!(f, "{{{:?} #{}}}", kind, val),
    }
  }
}

type AgentId = u8;
type SlotId = u8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Port(pub AgentId, pub SlotId);

impl Hash for Port {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.0.hash(state);
  }
}

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
  pub rewrites: usize,
}

impl Default for INet {
  fn default() -> Self {
    Self {
      nodes: vec![Agent::new(Port(0, 2), Port(0, 1), Port(0, 0), Era)],
      free: Vec::new(),
      rewrites: Default::default(),
    }
  }
}

impl INet {
  #[inline(always)]
  pub fn alloc(&mut self, kind: AgentKind) -> AgentId {
    match self.free.pop() {
      Some(id) => {
        self.nodes[id as usize] = Agent::with_id(id, kind);
        id
      }
      None => {
        let id = self.nodes.len() as AgentId;
        self.nodes.push(Agent::with_id(id, kind));
        id
      }
    }
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

    match (a_kind, b_kind) {
      (Op1 { .. }, ..) => self.ope1(a, b),
      (.., Op1 { .. }) => self.ope1(b, a),

      (Era, Con) => self.comm(a_kind, b_kind, a, b),
      (Con, Era) => self.comm(b_kind, a_kind, b, a),

      (Con, Dup { .. }) => self.comm(a_kind, b_kind, a, b),
      (Dup { .. }, Con) => self.comm(a_kind, b_kind, a, b),

      (Era, Dup { .. }) => self.comm(a_kind, b_kind, a, b),
      (Dup { .. }, Era) => self.comm(a_kind, b_kind, a, b),

      (Con, Con) => self.anni(a, b),
      (Dup { .. }, Dup { .. }) => self.anni(a, b),

      (Num { .. }, Num { .. }) => todo!(),

      (Con, Num { .. }) => todo!(),
      (Num { .. }, Con) => todo!(),

      (Dup { .. }, Num { .. }) => self.comm(a_kind, b_kind, a, b),
      (Num { .. }, Dup { .. }) => self.comm(b_kind, a_kind, b, a),

      (Era, Num { .. }) => todo!(),
      (Num { .. }, Era) => todo!(),

      (Era, Era) => todo!(),

      (Op2 { .. }, Num { .. }) => self.ope2(a, b),
      (Num { .. }, Op2 { .. }) => self.ope2(b, a),

      (Op2 { .. }, Con) => self.comm(a_kind, b_kind, a, b),
      (Con, Op2 { .. }) => self.comm(b_kind, a_kind, b, a),

      (Era, Op2 { .. }) => todo!(),
      (Op2 { .. }, Era) => todo!(),

      (Op2 { .. }, Dup { .. }) => self.comm(a_kind, b_kind, a, b),
      (Dup { .. }, Op2 { .. }) => self.comm(b_kind, a_kind, b, a),

      (Op2 { .. }, Op2 { .. }) => todo!(),
    }
  }

  #[inline(always)]
  fn anni(&mut self, a: AgentId, b: AgentId) {
    let a_aux = self.enter(Port::aux1(a));
    let b_aux = self.enter(Port::aux1(b));
    self.link(a_aux, b_aux);
    let a_aux = self.enter(Port::aux2(a));
    let b_aux = self.enter(Port::aux2(b));
    self.link(a_aux, b_aux);

    self.free.push(a);
    self.free.push(b);
  }

  #[inline(always)]
  fn comm(
    &mut self,
    a_kind: AgentKind,
    b_kind: AgentKind,
    a: AgentId,
    b: AgentId,
  ) {
    let a_new = self.alloc(a_kind);
    let b_new = self.alloc(b_kind);

    let aux = self.enter(Port::aux1(a));
    self.link(Port::main(b_new), aux);
    let aux = self.enter(Port::aux2(a));
    self.link(Port::main(b), aux);
    let aux = self.enter(Port::aux1(b));
    self.link(Port::main(a_new), aux);
    let aux = self.enter(Port::aux2(b));
    self.link(Port::main(a), aux);
    self.link(Port::aux1(a_new), Port::aux1(b_new));
    self.link(Port::aux2(a_new), Port::aux1(b));
    self.link(Port::aux1(a), Port::aux2(b_new));
    self.link(Port::aux2(a), Port::aux2(b))
  }

  #[inline(always)]
  pub fn ope2(&mut self, a: AgentId, b: AgentId) {
    let mut p1 = Port::main(a);
    let mut p2 = Port::main(b);
    let op = self.agent_kind(p1.agent());
    let l = self.agent_kind(p2.agent());

    match (op, l) {
      (Op2 { kind }, Num { val }) => {
        let op1 = self.alloc(Op1 { kind, val });

        let p1 = self.enter(Port::aux1(a));
        self.link(Port::main(op1), p1);

        let aux = self.enter(Port::aux2(a));
        self.link(aux, Port::aux2(op1));
      }
      _ => unreachable!(),
    };

    self.free.push(a);
    self.free.push(b);
  }

  #[inline(always)]
  pub fn ope1(&mut self, a: AgentId, b: AgentId) {
    let mut p1 = Port::main(a);
    let mut p2 = Port::main(b);
    let op = self.agent_kind(p1.agent());
    let l = self.agent_kind(p2.agent());

    match (op, l) {
      (Op1 { kind, val }, Num { val: n }) => {
        let res = match kind {
          OpKind::Add => val + n,
          OpKind::Sub => val - n,
          OpKind::Mul => val * n,
          OpKind::Div => val / n,
          OpKind::Shl => val << n,
          OpKind::Shr => val >> n,
          OpKind::Not => !n,
          OpKind::Eql => (val == n) as isize,
          OpKind::Neq => (val != n) as isize,
        };

        let num = self.alloc(Num { val: res });

        let aux = self.enter(Port::aux2(a));
        self.link(aux, Port::main(num));
      }
      _ => unreachable!(),
    };

    self.free.push(a);
    self.free.push(b);
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
          self.rewrites += 1;
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
        warp.push(Port::aux1(next.agent()));
        warp.push(Port::aux2(next.agent()));
      }
    }
  }
}

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
            let name = name_of(inet, Port::aux1(next.agent()), var_name);
            let port = inet.enter(Port::aux1(next.agent()));
            let body = reader(inet, port, var_name, dups_vec, dups_set, seen);
            let _ = inet.enter(Port::aux1(next.agent()));
            Term::Lam(name, Box::new(body))
          }
          1 => Term::Var(name_of(inet, next, var_name)),
          _ => {
            let port = inet.enter(Port::main(next.agent()));
            let func = reader(inet, port, var_name, dups_vec, dups_set, seen);
            let port = inet.enter(Port::aux1(next.agent()));
            let argm = reader(inet, port, var_name, dups_vec, dups_set, seen);
            Term::App(Box::new(func), Box::new(argm))
          }
        },
        Dup { label: _ } => match next.slot() {
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
        Num { val } => Term::Num(val),
        Op2 { .. } => unreachable!(),
        Op1 { .. } => unreachable!(),
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

    while let Some(dup) = dups_vec.pop() {
      let val = reader(
        self,
        dup,
        &mut binder_name,
        &mut dups_vec,
        &mut dups_set,
        &mut seen,
      );

      if let Dup { label } = self.agent_kind(dup.agent()) {
        let first = name_of(self, Port::aux1(label), &mut binder_name);
        let second = name_of(self, Port::aux2(label), &mut binder_name);

        main = Term::Dup(first, second, Box::new(val), Box::new(main));
      }
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
      .then(term.clone().repeated())
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

impl INet {
  fn encode(
    &mut self,
    term: &Term,
    up: Port,
    scope: &mut HashMap<String, Port>,
    vars: &mut Vec<(String, Port)>,
    dup_count: &mut u8,
  ) -> Port {
    match term {
      Term::Era => {
        let era = self.alloc(Era);
        self.link(Port::aux1(era), Port::aux2(era));
        Port::main(era)
      }
      Term::Var(name) => {
        vars.push((name.clone(), up));
        up
      }
      Term::Lam(name, body) => {
        let lam = self.alloc(Con);
        scope.insert(name.clone(), Port::aux1(lam));

        let body = self.encode(body, Port::aux2(lam), scope, vars, dup_count);
        self.link(Port::aux2(lam), body);

        Port::main(lam)
      }
      Term::App(func, argm) => {
        let app = self.alloc(Con);

        let func = self.encode(func, Port::main(app), scope, vars, dup_count);
        self.link(Port::main(app), func);

        let argm = self.encode(argm, Port::aux1(app), scope, vars, dup_count);
        self.link(Port::aux1(app), argm);

        Port::aux2(app)
      }
      Term::Sup(first, second) => {
        let dup = self.alloc(Dup { label: 0 });

        let first = self.encode(first, Port::aux1(dup), scope, vars, dup_count);
        self.link(Port::aux1(dup), first);

        let second =
          self.encode(second, Port::aux2(dup), scope, vars, dup_count);
        self.link(Port::aux2(dup), second);

        Port::main(dup)
      }
      Term::Dup(first, second, val, next) => {
        let dup = self.alloc(Dup { label: *dup_count });
        *dup_count += 1;

        scope.insert(first.clone(), Port::aux1(dup));
        scope.insert(second.clone(), Port::aux2(dup));

        let val = self.encode(val, Port::main(dup), scope, vars, dup_count);
        self.link(val, Port::main(dup));

        self.encode(next, up, scope, vars, dup_count)
      }
      Term::Num(val) => {
        let num = self.alloc(Num { val: *val });

        self.link(Port::aux1(num), Port::aux2(num));
        Port::main(num)
      }
      Term::Ope(op, l, r) => {
        let ope = self.alloc(Op2 { kind: *op });

        let func = self.encode(l, Port::main(ope), scope, vars, dup_count);
        self.link(Port::main(ope), func);

        let argm = self.encode(r, Port::aux1(ope), scope, vars, dup_count);
        self.link(Port::aux1(ope), argm);

        Port::aux2(ope)
      }
    }
  }

  pub fn inject(&mut self, term: &Term, host: Port) {
    let mut vars = Vec::new();
    let mut scope = HashMap::new();
    let dup_count = &mut 1;

    let main = self.encode(term, host, &mut scope, &mut vars, dup_count);

    for (ref name, var) in vars {
      match scope.get(name) {
        Some(next) => {
          let next = *next;
          if self.enter(next) == next {
            self.link(var, next);
          } else {
            println!("scope: {:?}", scope);
            panic!("Variable '{name}' used more than once.");
          }
        }
        None => panic!("Unbound variable '{name}'."),
      }
    }

    for (_, port) in scope {
      if self.enter(port) == port {
        let era = self.alloc(Era);
        self.link(Port::aux1(era), Port::aux2(era));
        self.link(port, Port::main(era));
      }
    }

    self.link(host, main);
  }
}

impl Term {
  pub fn to_net(&self) -> INet {
    let mut inet = INet::default();
    inet.inject(self, ROOT);
    inet
  }
}

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

    let res = parser().parse(line);

    match res {
      Ok(term) => {
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

  // let mut inet = INet::default();

  // inet.nodes = vec![
  //   Agent::new(Port(0, 2), Port(0, 1), Port(0, 0), Con),
  //   Agent::new(Port(0, 0), Port(0, 0), Port(0, 0), Con),
  //   Agent::new(Port(0, 0), Port(0, 0), Port(0, 0), Con),
  //   Agent::new(Port(0, 0), Port(0, 0), Port(0, 0), Con),
  // ];

  // inet.link(Port::aux1(0), Port::aux2(1));
  // inet.link(Port::aux1(1), Port::aux1(2));
  // inet.link(Port::aux2(2), Port::main(3));
  // inet.link(Port::aux1(3), Port::aux2(3));
  // inet.link(Port::main(1), Port::main(2));

  // inet.normal();
  // println!("{}", inet.term_of());
}
