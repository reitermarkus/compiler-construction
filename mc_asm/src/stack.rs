use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::VecDeque;

use crate::register::*;
use crate::storage::*;

#[derive(Debug)]
pub struct Stack {
  pub temporary_register: BTreeMap<usize, Reg32>,
  pub temporaries: VecDeque<Reg32>,
  pub lookup_table: HashMap<usize, (usize, bool, bool)>,
  pub parameters: Vec<(StorageType, usize, usize)>,
  pub parameters_size: usize,
  pub stack_size_index: usize,
  pub variables: Vec<(StorageType, usize, usize)>,
  pub variables_size: usize,
  pub used_registers: BTreeMap<Reg32, usize>,
}

impl Default for Stack {
  fn default() -> Stack {
    Stack {
      temporary_register: Default::default(),
      temporaries: VecDeque::from(vec![Reg32::EAX, Reg32::EDX, Reg32::ECX, Reg32::EBX, Reg32::EDI, Reg32::ESI]),
      lookup_table: Default::default(),
      parameters: Default::default(),
      parameters_size: 8,
      stack_size_index: Default::default(),
      variables: Default::default(),
      variables_size: Default::default(),
      used_registers: Default::default(),
    }
  }
}

impl Stack {
  pub fn lookup(&self, index: usize) -> (StorageType, usize, usize, bool, bool) {
    let &(i, parameter, array) = self.lookup_table.get(&index).unwrap();

    let (ty, count, offset) = if parameter { self.parameters[i] } else { self.variables[i] };

    (ty, count, offset, parameter, array)
  }

  pub fn push(
    &mut self,
    index: usize,
    storage_type: StorageType,
    count: usize,
    parameter: bool,
    array: bool,
  ) -> Pointer {
    if parameter {
      let offset = self.parameters_size;
      self.parameters.push((storage_type, count, self.parameters_size));
      self.lookup_table.insert(index, (self.parameters.len() - 1, true, array));

      if array {
        self.parameters_size += StorageType::Dword.size();
      } else {
        self.parameters_size += count * storage_type.size();
      }

      Pointer { base: Reg32::EBP, storage_type: StorageType::Dword, offset, index_offset: None, parameter, array }
    } else {
      self.variables_size += count * storage_type.size();
      self.variables.push((storage_type, count, self.variables_size));
      self.lookup_table.insert(index, (self.variables.len() - 1, false, array));
      Pointer { base: Reg32::EBP, storage_type, offset: self.variables_size, index_offset: None, parameter, array }
    }
  }
}

pub fn push_storage_temporary(storage: Storage, stack: &mut Stack) {
  if let Storage::Register(_, reg) = storage {
    push_temporary(reg, stack);
  }
}

pub fn push_temporary(temporary: Reg32, stack: &mut Stack) {
  stack.used_registers.remove(&temporary);

  if temporary == Reg32::EAX || temporary == Reg32::EDX || temporary == Reg32::ECX || temporary == Reg32::EBX {
    stack.temporaries.push_front(temporary);
  } else {
    stack.temporaries.push_back(temporary);
  }
}