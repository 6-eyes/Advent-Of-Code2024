mod solution;

pub fn init() -> Result<(), Box<dyn std::error::Error>> {
    let mut args  = std::env::args();
    args.next();

    let day = args.next().expect(r#"Which day to solve? Run 'cargo run -- ${day number} ${part number}'."#).parse::<u8>()?;
    let part = Part::parse(args.next().expect(r#"Which part to solve? Run 'cargo run -- ${day number} ${part number}'"#))?;
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

    println!("ans: {ans}. Time taken {elapsed:?}");
    Ok(())
}

fn get_solution(day: u8) -> Box<dyn Solution> {
    match day {
        1 => Box::new(solution::Day1),
        2 => Box::new(solution::Day2),
        _ => panic!("Day yet to come!"),
    }
}

trait Solution {
    fn part_1(&self, input: String) -> Result<usize, Error>;
    fn part_2(&self, input: String) -> Result<usize, Error>;
}

#[derive(Debug)]
enum Error {
    InvalidInput(String),
    InvalidArgument,
}

impl std::error::Error for Error {}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidArgument => write!(f, "Invalid argument passed."),
            Self::InvalidInput(reason) => write!(f, "Input invalid. {reason}"),
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
