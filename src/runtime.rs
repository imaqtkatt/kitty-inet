use std::fmt;
use AgentKind::*;

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum AgentKind {
  Era,
  Con,
  Bol { val: bool },
  Dup { label: u8 },
  Num { val: isize },
  Op2 { kind: OpKind },
  Op1 { kind: OpKind, val: isize },
  Cnd,
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
      Bol { val } => write!(f, "%{val}"),
      Dup { label } => write!(f, "dup({label})"),
      Num { val } => write!(f, "#{}", val),
      Op2 { kind } => write!(f, "{:?}", kind),
      Op1 { kind, val } => write!(f, "{{{:?} #{}}}", kind, val),
      Cnd => write!(f, "cond"),
    }
  }
}

type AgentId = u8;
type SlotId = u8;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Port(pub AgentId, pub SlotId);

impl std::hash::Hash for Port {
  fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
    self.0.hash(state);
  }
}

pub const ROOT: Port = Port(0, 1);

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
    write!(f, "({} {})", self.0, self.1)
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
    write!(f, "{}~{}+{}#{}", self.main, self.aux1, self.aux2, self.kind)
  }
}

impl fmt::Debug for Agent {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{}~{}+{}#{}", self.main, self.aux1, self.aux2, self.kind)
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
  pub fn enter(&self, port: Port) -> Port {
    self.nodes[port.agent() as usize].port(port.slot())
  }

  #[inline(always)]
  pub fn agent_kind(&self, id: AgentId) -> AgentKind {
    self.nodes[id as usize].kind
  }

  #[inline(always)]
  pub fn agent_is_truthy(&self, id: AgentId) -> bool {
    match self.nodes[id as usize].kind {
      Era => false,
      Num { val } => val == 1,
      Bol { val } => val,
      Con => todo!(),
      Dup { label } => todo!(),
      Op2 { kind } => todo!(),
      Op1 { kind, val } => todo!(),
      Cnd => todo!(),
    }
  }

  #[inline(always)]
  pub fn rewrite(&mut self, a: AgentId, b: AgentId) {
    let a_kind = self.agent_kind(a);
    let b_kind = self.agent_kind(b);

    match (a_kind, b_kind) {
      (Cnd, ..) => self.cond(a, b),
      (.., Cnd) => todo!(),
      
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
      
      (Con, Num { .. }) => self.comm(a_kind, b_kind, a, b),
      (Num { .. }, Con) => self.comm(b_kind, a_kind, b, a),
      
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

      (Con, Bol { .. }) => self.bool(a, b),
      (Bol { .. }, Con) => self.bool(b, a),

      (Bol { .. }, ..) => self.comm(a_kind, b_kind, a, b),
      (.., Bol { .. }) => self.comm(a_kind, b_kind, a, b),
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

    self.free(a);
    self.free(b);
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
  pub fn ope2(&mut self, operator: AgentId, number: AgentId) {
    let mut p1 = Port::main(operator);
    let mut p2 = Port::main(number);
    let op = self.agent_kind(p1.agent());
    let l = self.agent_kind(p2.agent());

    match (op, l) {
      (Op2 { kind }, Num { val }) => {
        let op1 = self.alloc(Op1 { kind, val });

        let p1 = self.enter(Port::aux1(operator));
        self.link(Port::main(op1), p1);

        let aux = self.enter(Port::aux2(operator));
        self.link(aux, Port::aux2(op1));
      }
      _ => unreachable!(),
    };

    self.free(operator);
    self.free(number);
  }

  #[inline(always)]
  pub fn ope1(&mut self, operator: AgentId, number: AgentId) {
    let mut p1 = Port::main(operator);
    let mut p2 = Port::main(number);
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

        let aux = self.enter(Port::aux2(operator));
        self.link(aux, Port::main(num));
      }
      _ => unreachable!(),
    };

    self.free(operator);
    self.free(number);
  }

  #[inline(always)]
  pub fn cond(&mut self, cnd: AgentId, other: AgentId) {
    let cond = self.enter(Port::main(cnd));
    let is_truthy = self.agent_is_truthy(cond.agent());
    let branches = self.enter(Port::aux2(cnd));
    let up = self.enter(Port::aux1(cnd));
    let truthy = self.enter(Port::aux1(branches.agent()));
    let falsy = self.enter(Port::aux2(branches.agent()));

    let era = self.alloc(Era);

    if is_truthy {
      self.link(falsy, Port::main(era));
      self.link(truthy, up);
    } else {
      self.link(truthy, Port::main(era));
      self.link(falsy, up);
    }

    self.free(cnd);
    self.free(other);
  }

  #[inline(always)]
  pub fn bool(&mut self, app: AgentId, bol: AgentId) {
    let enter_a = self.enter(Port::aux1(app));
    let a = self.agent_kind(enter_a.agent());
    let b = self.agent_kind(bol);
    let up = self.enter(Port::aux2(app));

    let mut new_bol = false;
    match (a, b) {
      (Bol { val: b1 }, Bol { val: b2 }) => {
        if b1 == true && b2 == true {
          new_bol = false
        } else if b1 == false && b2 == false {
          new_bol = true
        } else {
          new_bol = false
        }
      }
      _ => panic!(),
    }
    let new_bol = self.alloc(Bol { val: new_bol });
    self.link(Port::main(new_bol), up);

    self.free(app);
    self.free(bol);
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
