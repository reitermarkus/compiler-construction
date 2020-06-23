use std::fmt;

use mc_parser::ast::Ty;

use crate::register::*;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum StorageType {
  Qword,
  Dword,
  Byte,
}

impl From<&Ty> for StorageType {
  /// Gets the [`StorageType`](crate::ast::Ty) from the [`Ty`](crate::ast::Ty).
  fn from(ty: &Ty) -> Self {
    match ty {
      Ty::Float => Self::Dword,
      Ty::Int => Self::Dword,
      Ty::Bool => Self::Byte,
      Ty::String => Self::Dword,
    }
  }
}

impl fmt::Display for StorageType {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Qword => "QWORD PTR",
      Self::Dword => "DWORD PTR",
      Self::Byte => "BYTE PTR",
    }
    .fmt(f)
  }
}

impl StorageType {
  /// Returns the size of the pointer.
  pub fn size(self) -> usize {
    match self {
      Self::Qword => 8,
      Self::Dword => 4,
      Self::Byte => 1,
    }
  }

  /// Maps the [`Reg32`](crate::register::Reg32) register to a string.
  pub fn map_register(self, reg: Reg32) -> String {
    match self {
      Self::Dword => reg.to_string(),
      Self::Byte => reg.as_reg8().0.to_string(),
      _ => unreachable!(),
    }
  }
}

#[derive(Debug, Clone)]
pub struct Pointer {
  pub base: Reg32,
  pub storage_type: StorageType,
  pub offset: usize,
  pub index_offset: Option<Offset>,
  pub parameter: bool,
  pub array: bool,
}

impl fmt::Display for Pointer {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "{} [{}", self.storage_type, self.base)?;

    if self.offset != 0 {
      if self.parameter { "+" } else { "-" }.fmt(f)?;

      write!(f, "{}", self.offset)?;
    }
    if let Some(index_offset) = &self.index_offset {
      write!(f, "+{}*{}", index_offset, self.storage_type.size())?;
    }

    write!(f, "]")
  }
}

#[derive(Debug, Clone)]
pub enum Storage {
  Pointer(Pointer),
  Register(StorageType, Reg32),
  Fpu(StorageType),
  Literal(StorageType, String),
  Label(StorageType, String, bool),
}

impl fmt::Display for Storage {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Pointer(pointer) => write!(f, "{}", pointer),
      Self::Register(storage_type, reg) => {
        if f.alternate() {
          write!(f, "{}", storage_type.map_register(*reg))
        } else {
          write!(f, "{}", reg)
        }
      }
      Self::Fpu(_) => unreachable!(),
      Self::Literal(_, string) => write!(f, "{}", string),
      Self::Label(ty, label, flat) => {
        if *flat {
          write!(f, "OFFSET FLAT:{}", label)
        } else {
          write!(f, "{} {}", ty, label)
        }
      }
    }
  }
}

#[derive(Debug, Clone)]
pub enum Offset {
  Register(Reg32),
  Literal(usize),
}

impl fmt::Display for Offset {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::Register(reg) => reg.fmt(f),
      Self::Literal(lit) => lit.fmt(f),
    }
  }
}

impl Storage {
  /// Returns the [`StorageType`](storage::StorageType) from the [`Storage`](storage::Storage).
  pub fn storage_type(&self) -> StorageType {
    match *self {
      Self::Pointer(Pointer { storage_type, .. }) => storage_type,
      Self::Register(storage_type, _) => storage_type,
      Self::Fpu(storage_type) => storage_type,
      Self::Literal(storage_type, _) => storage_type,
      Self::Label(storage_type, ..) => storage_type,
    }
  }
}
