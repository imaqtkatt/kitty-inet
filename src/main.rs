use std::fmt;

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

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Port(pub AgentId, pub SlotId);

const ROOT: Port = Port(0, 0);

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
      if next == ROOT {
        warp.push(Port(next.agent(), 1));
        warp.push(Port(next.agent(), 2));
      }
    }
  }
}

fn main() {
  println!("Hello, world!");
}
