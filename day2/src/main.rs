use day2::{Interpreter, ProgramError};

fn run_1(path: &str) -> Result<u32, ProgramError> {
    let mut i = Interpreter::read_from_file(path)?;
    i.write_to(1, 12)?;
    i.write_to(2, 2)?;
    i.run_program()?;
    i.read_from(0)
}

fn run_2(path: &str) -> Result<u32, ProgramError> {
    const EXPECTED: u32 = 19690720;
    let mut i = Interpreter::read_from_file(path)?;

    let mut result = 0;
    'outer: for noun in 0..=99 {
        for verb in 0..=99 {
            i.write_to(1, noun)?;
            i.write_to(2, verb)?;
            match i.run_program() {
                Ok(_) => {
                    let value = i.read_from(0)?;
                    if value == EXPECTED {
                        result = 100 * noun + verb;
                        break 'outer;
                    }
                },
                Err(e) => {
                    println!("{} {}: {:?}", noun, verb, e);
                }
            }
            i.reset();
        }
    }
    Ok(result)
}

fn main() {
    println!("Result: {:?}", run_1("./input_1").unwrap());
    println!("Result: {:?}", run_2("./input_2").unwrap());
}
