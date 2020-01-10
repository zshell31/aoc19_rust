use std::cmp;
use std::error;
use std::fs::File;
use std::io::{self, BufRead};
use std::path::Path;

type Result<T> = std::result::Result<T, Box<dyn error::Error>>;

fn read_lines<P>(filename: P) -> io::Result<io::Lines<impl BufRead>>
where
    P: AsRef<Path>,
{
    let file = File::open(filename)?;
    Ok(io::BufReader::new(file).lines())
}

fn calc_fuel(mass: i32) -> i32 {
    let fuel = mass / 3 - 2;
    cmp::max(fuel, 0)
}

fn calc_full_fuel(mass: i32) -> i32 {
    let mut total = 0;
    let mut fuel = mass;
    while fuel > 0 {
        fuel = calc_fuel(fuel);
        total += fuel;
    }
    total
}

fn calc_fuel_for_input<P, F>(filename: P, calculation: F) -> Result<i32>
where
    P: AsRef<Path>,
    F: Fn(i32) -> i32,
{
    // let lines = read_lines(filename.as_ref()).expect(&format!(
    //     "Error during reading file {:?}",
    //     filename.as_ref().to_str()
    // ));
    let lines = read_lines(filename.as_ref())?;
    let mut total = 0;
    for line in lines {
        let mass = line?.parse::<i32>()?;
        total += calculation(mass);
    }

    Ok(total)
}

fn print_result<F>(prefix: &str, path: &str, calculation: F)
where
    F: Fn(i32) -> i32,
{
    match calc_fuel_for_input(path, calculation) {
        Ok(result) => println!("{} Total: {}", prefix, result),
        Err(e) => println!("{} Error: {}", prefix, e),
    }
}

fn main() {
    let path = "./input";
    print_result("V1", path, calc_fuel);
    print_result("V2", path, calc_full_fuel);
}
