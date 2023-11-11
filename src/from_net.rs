use std::collections::{HashMap, HashSet};

use crate::{
  runtime::{AgentKind::*, INet, OpKind, Port, ROOT},
  term::Term,
};

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
        Cnd => {
          let cond_port = inet.enter(Port::main(next.agent()));
          let cond =
            reader(inet, cond_port, var_name, dups_vec, dups_set, seen);

          let branches = inet.enter(Port::aux2(next.agent()));

          let then_port = inet.enter(Port::aux1(branches.agent()));
          let r#then =
            reader(inet, then_port, var_name, dups_vec, dups_set, seen);

          let else_port = inet.enter(Port::aux2(branches.agent()));
          let r#else =
            reader(inet, else_port, var_name, dups_vec, dups_set, seen);

          Term::If(Box::new(cond), Box::new(r#then), Box::new(r#else))
        }
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
