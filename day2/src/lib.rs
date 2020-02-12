use std::fs;
use std::io;
use std::num;
use std::path::Path;

#[derive(Debug)]
pub enum ProgramError {
    IoError(io::Error),
    ParseError(num::ParseIntError),
    InvalidAddress(usize),
    InvalidOpcode(u32),
    InvalidInstruction(usize),
}

impl From<io::Error> for ProgramError {
    fn from(error: io::Error) -> Self {
        ProgramError::IoError(error)
    }
}

impl From<num::ParseIntError> for ProgramError {
    fn from(error: num::ParseIntError) -> Self {
        ProgramError::ParseError(error)
    }
}

const MAX_MEMORY_SIZE: usize = 16000;

const ADD_OP: u32 = 1;
const MUL_OP: u32 = 2;
const HALT_OP: u32 = 99;

#[derive(Debug)]
pub struct Interpreter {
    codes: Vec<u32>,
    memory: Vec<u32>,
}

impl Interpreter {
    fn new(codes: Option<Vec<u32>>) -> Self {
        match codes {
            Some(_codes) => {
                let memory = _codes.clone();
                Interpreter {
                    codes: _codes,
                    memory: memory,
                }
            }
            None => Interpreter {
                codes: vec![],
                memory: vec![],
            },
        }
    }

    pub fn read_from_file<P>(filename: P) -> Result<Self, ProgramError>
    where
        P: AsRef<Path>,
    {
        Interpreter::read_from_string(fs::read_to_string(filename)?)
    }

    pub fn read_from_string(content: String) -> Result<Self, ProgramError> {
        let input = content.trim_end();

        if input.is_empty() {
            Ok(Interpreter::new(None))
        } else {
            let codes = input
                .split(',')
                .map(|c| c.parse::<u32>().map_err(|e| e.into()))
                .collect::<Result<Vec<u32>, ProgramError>>()?;

            Ok(Interpreter::new(Some(codes)))
        }
    }

    fn ensure_memory_available(&mut self, address: usize) {
        if address < MAX_MEMORY_SIZE && address >= self.memory.len() {
            self.memory.resize(address + 1, 0);
        }
    }

    pub fn read_from(&mut self, address: usize) -> Result<u32, ProgramError> {
        self.ensure_memory_available(address);
        self.memory
            .get(address)
            .copied()
            .ok_or(ProgramError::InvalidAddress(address))
    }

    pub fn write_to(&mut self, address: usize, value: u32) -> Result<u32, ProgramError> {
        self.ensure_memory_available(address);
        let elem = self
            .memory
            .get_mut(address)
            .ok_or(ProgramError::InvalidAddress(address))?;
        let old = *elem;
        *elem = value;
        Ok(old)
    }

    fn add_instruction(&mut self, eip: usize) -> Result<usize, ProgramError> {
        match eip {
            x if x + 4 <= self.memory.len() => {
                let v1 = self.read_from(self.memory[eip + 1] as usize)?;
                let v2 = self.read_from(self.memory[eip + 2] as usize)?;
                self.write_to(self.memory[eip + 3] as usize, v1.saturating_add(v2))?;
                Ok(eip + 4)
            }
            _ => Err(ProgramError::InvalidInstruction(eip)),
        }
    }

    fn mul_instruction(&mut self, eip: usize) -> Result<usize, ProgramError> {
        match eip {
            x if x + 4 <= self.memory.len() => {
                let v1 = self.read_from(self.memory[eip + 1] as usize)?;
                let v2 = self.read_from(self.memory[eip + 2] as usize)?;
                self.write_to(self.memory[eip + 3] as usize, v1.saturating_mul(v2))?;
                Ok(eip + 4)
            }
            _ => Err(ProgramError::InvalidInstruction(eip)),
        }
    }

    pub fn run_program(&mut self) -> Result<(), ProgramError> {
        let mut eip = 0;
        let mut result = Ok(());
        while eip < self.memory.len() {
            match self.memory[eip] {
                ADD_OP => {
                    eip = self.add_instruction(eip)?;
                }
                MUL_OP => {
                    eip = self.mul_instruction(eip)?;
                }
                HALT_OP => break,
                _ => {
                    result = Err(ProgramError::InvalidOpcode(self.memory[eip]));
                    break;
                }
            }
        }

        result
    }

    pub fn reset(&mut self) {
        self.memory = self.codes.clone();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_error {
        ($e:expr, $pat:pat) => {
            match $e {
                Err($pat) => (),
                Err(ref e) => panic!(
                    "assertion failed: `{:?}` does not match `{}`",
                    e,
                    stringify!($pat)
                ),
                ref ok => panic!("assertion failed: expected error, got `{:?}`", ok),
            }
        };
        ($e:expr, $pat:pat if $cond:expr) => {
            match $e {
                Err($pat) if $cond => (),
                Err(ref e) => panic!(
                    "assertion failed: `{:?}` does not match `{}`",
                    e,
                    stringify!($pat)
                ),
                ref ok => panic!("assertion failed: expected error, got `{:?}`", ok),
            }
        };
    }

    #[test]
    fn test_parse_error() {
        let content = "1,2,3,a,4,5".to_string();
        let result = Interpreter::read_from_string(content);
        assert_error!(result, ProgramError::ParseError(_));
    }

    #[test]
    fn test_parse_empty_program() {
        let content = "".to_string();
        let result = Interpreter::read_from_string(content);
        assert!(result.is_ok());
    }

    #[test]
    fn test_read_from() {
        let mut i = Interpreter::new(Some(vec![1, 2, 3, 4, 5]));
        assert_eq!(i.read_from(4).unwrap(), 5);
    }

    #[test]
    fn test_read_from_with_resizing() {
        let mut i = Interpreter::new(None);
        assert_eq!(i.read_from(1000).unwrap(), 0);
    }

    #[test]
    fn test_read_from_invalid_address() {
        let address = MAX_MEMORY_SIZE;
        let mut i = Interpreter::new(None);
        assert_error!(i.read_from(address), ProgramError::InvalidAddress(a) if a == address);
    }

    #[test]
    fn test_write_to() {
        let mut i = Interpreter::new(Some(vec![1, 2, 3, 4, 6]));
        assert_eq!(i.read_from(4).unwrap(), 6);
        assert!(i.write_to(4, 5).is_ok());
        assert_eq!(i.read_from(4).unwrap(), 5);
    }

    #[test]
    fn test_write_to_with_resizing() {
        let mut i = Interpreter::new(None);
        assert_eq!(i.read_from(1000).unwrap(), 0);
        assert!(i.write_to(1000, 5).is_ok());
        assert_eq!(i.read_from(1000).unwrap(), 5);
    }

    #[test]
    fn test_write_to_invalid_address() {
        let mut i = Interpreter::new(None);
        let address = MAX_MEMORY_SIZE;
        assert_error!(i.write_to(address, 5), ProgramError::InvalidAddress(a) if a == address);
    }

    #[test]
    fn test_add_program() {
        let mut i = Interpreter::read_from_string("1,3,3,3".to_string()).unwrap();
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(3).unwrap(), 6);
    }

    #[test]
    fn test_mul_program() {
        let mut i = Interpreter::read_from_string("2,3,3,3".to_string()).unwrap();
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(3).unwrap(), 9);
    }

    #[test]
    fn test_hlt_program() {
        let mut i = Interpreter::read_from_string("1,3,0,3,99,2,1,3,3".to_string()).unwrap();
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(3).unwrap(), 4);
    }

    #[test]
    fn test_program_with_add_mul() {
        let mut i = Interpreter::read_from_string("1,3,0,3,2,1,3,3".to_string()).unwrap();
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(3).unwrap(), 12);
    }

    #[test]
    fn test_program_1() {
        let mut i =
            Interpreter::read_from_string("1,9,10,3,2,3,11,0,99,30,40,50".to_string()).unwrap();
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(0).unwrap(), 3500);
    }

    #[test]
    fn test_program_2() {
        let mut i = Interpreter::read_from_string("2,4,4,5,99".to_string()).unwrap();
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(5).unwrap(), 99 * 99);
    }

    #[test]
    fn test_program_3() {
        let mut i = Interpreter::read_from_string("1,1,1,4,99,5,6,0,99".to_string()).unwrap();
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(0).unwrap(), 30);
        assert_eq!(i.read_from(4).unwrap(), 2);
    }

    #[test]
    fn test_program_4() {
        let mut i = Interpreter::read_from_string("1,1,1,1000".to_string()).unwrap();
        assert_error!(i.run_program(), ProgramError::InvalidOpcode(0));
    }

    #[test]
    fn test_invalid_opcode() {
        let mut i = Interpreter::read_from_string("1,1,1,3,5,2,2,1".to_string()).unwrap();
        assert_error!(i.run_program(), ProgramError::InvalidOpcode(5));
    }

    #[test]
    fn test_invalid_add_instruction() {
        let mut i = Interpreter::read_from_string("1,1,1,3,1,2".to_string()).unwrap();
        assert_error!(i.run_program(), ProgramError::InvalidInstruction(4));
    }

    #[test]
    fn test_invalid_mul_instruction() {
        let mut i = Interpreter::read_from_string("1,1,1,3,2,2".to_string()).unwrap();
        assert_error!(i.run_program(), ProgramError::InvalidInstruction(4));
    }

    #[test]
    fn test_reset() {
        let mut i = Interpreter::read_from_string("1,3,3,3".to_string()).unwrap();
        assert_eq!(i.read_from(3).unwrap(), 3);
        assert!(i.run_program().is_ok());
        assert_eq!(i.read_from(3).unwrap(), 6);
        i.reset();
        assert_eq!(i.read_from(3).unwrap(), 3);
    }
}
