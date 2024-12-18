mod solution;

pub fn init() -> Result<(), Box<dyn std::error::Error>> {
    let mut args  = std::env::args();
    args.next();

    let info = "\n\nWhich day to solve? Run 'cargo run -- ${day number} ${part number}'\nTo initialize new files for new day run `cargo run -- ${day number} init\n\n";
    let day = args.next().expect(info).parse::<u8>().expect(info);

    let arg = args.next().expect("\n\nWhich part to solve? Run 'cargo run -- ${day number} ${part number}'\nTo initialize new files for new day run `cargo run -- ${day number} init`\n\n");
    
    if arg == "init" {
        return Ok(create(day)?);
    }

    let part = Part::parse(arg)?;
    let path = match args.next() {
        Some(arg) if arg == "test" => format!("input/day{day}-part{part}_test.txt"),
        Some(arg) => panic!("Invalid argument {} passed. Run 'cargo run -- 1 test' to run test code", arg),
        None => format!("input/day{day}-part{part}.txt"),
    };

    let input = std::fs::read_to_string(path)?;
    let sol = get_solution(day);

    let instant = std::time::Instant::now();
    let ans = match part {
        Part::One => sol.part_1(input)?,
        Part::Two => sol.part_2(input)?,
    };
    let elapsed = instant.elapsed();

    println!("ans: {ans} Time taken {elapsed:?}");
    Ok(())
}

fn create(day: u8) -> Result<(), std::io::Error> {
    let create = |file: String| -> Result<(), std::io::Error> {
        if !std::fs::exists(&file)? {
            std::fs::File::create(&file)?;
            println!("created file: {file}");
        }
        Ok(())
    };

    for part in 1..=2 {
        create(format!("input/day{day}-part{part}.txt"))?;
        create(format!("input/day{day}-part{part}_test.txt"))?;
    }

    Ok(())
}

fn get_solution(day: u8) -> Box<dyn Solution> {
    match day {
        1 => Box::new(solution::Day1),
        2 => Box::new(solution::Day2),
        3 => Box::new(solution::Day3),
        4 => Box::new(solution::Day4),
        5 => Box::new(solution::Day5),
        6 => Box::new(solution::Day6),
        7 => Box::new(solution::Day7),
        8 => Box::new(solution::Day8),
        9 => Box::new(solution::Day9),
        10 => Box::new(solution::Day10),
        11 => Box::new(solution::Day11),
        12 => Box::new(solution::Day12),
        13 => Box::new(solution::Day13),
        14 => Box::new(solution::Day14),
        15 => Box::new(solution::Day15),
        16 => Box::new(solution::Day16),
        17 => Box::new(solution::Day17),
        18 => Box::new(solution::Day18),
        // 19 => Box::new(solution::Day19),
        // 20 => Box::new(solution::Day20),
        // 21 => Box::new(solution::Day21),
        // 22 => Box::new(solution::Day22),
        // 23 => Box::new(solution::Day23),
        // 24 => Box::new(solution::Day24),
        // 25 => Box::new(solution::Day25),
        _ => panic!("Day yet to come!"),
    }
}

trait Solution {
    fn part_1(&self, input: String) -> Result<Box<dyn std::fmt::Display>, Error>;
    fn part_2(&self, input: String) -> Result<Box<dyn std::fmt::Display>, Error>;
}

#[derive(Debug)]
enum Error {
    InvalidArgument,
    InvalidInput(String),
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidArgument => write!(f, "Invalid argument passed."),
            Self::InvalidInput(s) => write!(f, "Invalid input.  {}", s)
        }
    }
}

enum Part {
    One,
    Two,
}

impl Part {
    fn parse(input: String) -> Result<Self, Error> {
        match input.as_str() {
            "1" | "One" | "one" | "ONE" => Ok(Self::One),
            "2" | "Two" | "two" | "TWO" => Ok(Self::Two),
             _ =>  Err(Error::InvalidArgument),
        }
    }
}

impl std::fmt::Display for Part {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{0}", match self {
            Self::One => "1",
            Self::Two => "2",
        })
    }
}
