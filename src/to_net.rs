use std::collections::HashMap;

use crate::{
  runtime::{AgentKind::*, INet, OpKind, Port, ROOT},
  term::Term,
};

impl Term {
  pub fn to_net(&self) -> INet {
    let mut inet = INet::default();
    inet.inject(self, ROOT);
    inet
  }
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

        let lhs = self.encode(l, Port::main(ope), scope, vars, dup_count);
        self.link(Port::main(ope), lhs);

        let rhs = self.encode(r, Port::aux1(ope), scope, vars, dup_count);
        self.link(Port::aux1(ope), rhs);

        Port::aux2(ope)
      }
      Term::If(cond, r#then, r#else) => {
        let r#if = self.alloc(Cnd);

        let cond = self.encode(cond, Port::main(r#if), scope, vars, dup_count);
        self.link(Port::main(r#if), cond);

        let con = self.alloc(Con);
        self.link(Port::aux2(r#if), Port::main(con));

        let r#then =
          self.encode(r#then, Port::aux1(con), scope, vars, dup_count);
        self.link(Port::aux1(con), r#then);

        let r#else =
          self.encode(r#else, Port::aux2(con), scope, vars, dup_count);
        self.link(Port::aux2(con), r#else);

        Port::aux1(r#if)
      }
      Term::Let(..) => unreachable!(),
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
