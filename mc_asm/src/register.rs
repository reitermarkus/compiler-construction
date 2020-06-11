use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Reg32 {
  EAX,
  ECX,
  EDX,
  EBX,
  ESP,
  EBP,
  ESI,
  EDI,
}

impl fmt::Display for Reg32 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::EAX => "eax",
      Self::EBX => "ebx",
      Self::ECX => "ecx",
      Self::EDX => "edx",
      Self::ESP => "esp",
      Self::EBP => "ebp",
      Self::EDI => "edi",
      Self::ESI => "esi",
    }
    .fmt(f)
  }
}

impl Reg32 {
  pub fn as_reg8(self) -> (Reg8, Reg8) {
    match self {
      Self::EAX => (Reg8::AL, Reg8::AH),
      Self::ECX => (Reg8::CL, Reg8::CH),
      Self::EDX => (Reg8::DL, Reg8::DH),
      Self::EBX => (Reg8::BL, Reg8::BH),
      _ => unreachable!(),
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub enum Reg8 {
  AL,
  CL,
  DL,
  BL,
  AH,
  CH,
  DH,
  BH,
}

impl fmt::Display for Reg8 {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::AL => "al",
      Self::CL => "cl",
      Self::DL => "dl",
      Self::BL => "bl",
      Self::AH => "ah",
      Self::CH => "ch",
      Self::DH => "dh",
      Self::BH => "bh",
    }
    .fmt(f)
  }
}
