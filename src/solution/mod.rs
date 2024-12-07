use super::{Solution, Error};
use std::collections::{HashMap, HashSet};

pub struct Day1;

impl Solution for Day1 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let mut re: (Vec<usize>, Vec<usize>) = input.lines().map(|l| {
            let mut s = l.split_whitespace();
            let parse = |s: Option<&str>| s.expect("invalid input").parse::<usize>().expect("unable to parse input");
            (parse(s.next()), parse(s.next()))
        }).unzip();

        re.0.sort();
        re.1.sort();

        let ans = re.0.into_iter().zip(re.1).map(|(v1, v2)| v1.abs_diff(v2)).sum::<usize>();

        Ok(ans)
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let re: (Vec<usize>, Vec<usize>) = input.lines().map(|l| {
            let mut s = l.split_whitespace();
            let parse = |s: Option<&str>| s.expect("invalid input").parse::<usize>().expect("unable to parse input");
            (parse(s.next()), parse(s.next()))
        }).unzip();

        let data = re.1.into_iter().fold(HashMap::<usize, (usize, usize)>::new(), |mut acc, val| {
            acc.entry(val).and_modify(|v| v.1 += 1).or_insert((0, 1));
            acc
        });

        Ok(re.0.into_iter().fold(data, |mut acc, val| {
            acc.entry(val).and_modify(|v| v.0 += 1);
            acc
        }).into_iter().map(|(k, (v1, v2))| k * v1 * v2).sum::<usize>())
    }
}

pub struct Day2;

impl Solution for Day2 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        Ok(input.lines().fold(0, |acc, l| {
            let nums = l.split_whitespace().map(|v| v.parse::<usize>().expect("unable to parse input. Input not a number!")).collect::<Vec<usize>>();
            let mut increasing = None;
            for win in nums.windows(2) {
                let (left, right) = (win[0], win[1]);
                let diff = right.abs_diff(left);
                if !(1..=3).contains(&diff) { return acc; }
                match increasing {
                    None => increasing = Some(right > left),
                    Some(true) => if right < left { return acc; },
                    Some(false) => if left < right { return acc; },
                };
            }
            acc + 1
        }))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        Ok(input.lines().fold(0, |acc, l| {
            let nums = l.split_whitespace().map(|v| v.parse::<usize>().expect("unable to parse input. Input not a number!")).collect::<Vec<usize>>();
            for i in 0..nums.len() {
                let nums = nums[0..i].iter().chain(&nums[i + 1..]).map(usize::to_owned).collect::<Vec<usize>>();
                if Self::valid_levels(nums) { return acc + 1 }
            }
            acc
        }))
    }
}

impl Day2 {
    fn valid_levels(levels: Vec<usize>) -> bool {
        let mut increasing = None;
        for win in levels.windows(2) {
            let (left, right) = (win[0], win[1]);
            let diff = right.abs_diff(left);
            if !(1..=3).contains(&diff) { return false; }
            match increasing {
                None => increasing = Some(right > left),
                Some(true) => if right < left { return false; },
                Some(false) => if left < right { return false; },
            };
        }

        true
    }
}

pub struct Day3;

impl Solution for Day3 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let initial = "mul(";
        let comma = ",";
        let end_parenthesis = ")";
        Ok(input.lines().fold(0, |mut acc, l| {
            let get_num = |start| {
                let num = &l[start..].chars().take_while(char::is_ascii_digit).collect::<String>();
                num.parse::<usize>().ok().map(|v| (v, num.len()))
            };

            let mut idx = 0;
            // min length is mul(0,0), i.e. 4 more than initials. Plus 1 for getting index.
            while idx <= l.len() - initial.len() - 4 {
                if l[idx..].starts_with(initial) {
                    idx += initial.len();

                    if let Some((first, len)) = get_num(idx) {
                        idx += len;

                        if &l[idx..idx + 1] == comma {
                            idx += comma.len();
                            if let Some((second, len)) = get_num(idx) {
                                idx += len;

                                if &l[idx..idx + 1] == end_parenthesis {
                                    idx += end_parenthesis.len();
                                    acc += first * second;
                                }
                            }
                        }
                    }
                }
                else {
                    idx += 1;
                }
            }
            acc
        }))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let initial = "mul(";
        let do_instruction = "do()";
        let dont_instruction = "don't()";
        let comma = ",";
        let end_parenthesis = ")";

        let mut enabled = true;
        Ok(input.lines().fold(0, |mut acc, l| {
            let get_num = |start| {
                let num = &l[start..].chars().take_while(char::is_ascii_digit).collect::<String>();
                num.parse::<usize>().ok().map(|v| (v, num.len()))
            };

            let mut idx = 0;
            // min length is mul(0,0), i.e. 4 more than initials. Plus 1 for getting index.
            while idx <= l.len() - initial.len() - 4 {
                if l[idx..].starts_with(do_instruction) {
                    enabled = true;
                    idx += do_instruction.len();
                }
                else if l[idx..].starts_with(dont_instruction) {
                    enabled = false;
                    idx += dont_instruction.len();
                }

                if enabled && l[idx..].starts_with(initial) {
                    idx += initial.len();

                    if let Some((first, len)) = get_num(idx) {
                        idx += len;

                        if &l[idx..idx + 1] == comma {
                            idx += comma.len();
                            if let Some((second, len)) = get_num(idx) {
                                idx += len;

                                if &l[idx..idx + 1] == end_parenthesis {
                                    idx += end_parenthesis.len();
                                    acc += first * second;
                                }
                            }
                        }
                    }
                }
                else {
                    idx += 1;
                }
            }
            acc
        }))
    }
}

pub struct Day4;

impl Solution for Day4 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let word = "XMAS";
        let grid = input.lines().map(|l| l.chars().collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();
        let w = grid.first().expect("invalid input").len() as isize;
        let h = grid.len() as isize;
        let char_at = |x: isize, y: isize| grid[y as usize][x as usize];

        let directions = [-1, 0, 1].into_iter().flat_map(|y| [-1, 0, 1].into_iter().map(move |x| (x, y))).filter(|&(x, y)| x != 0 || y != 0).collect::<Vec<(isize, isize)>>();
        let word_vec = word.chars().collect::<Vec<char>>();

        Ok((0..h).fold(0, |h_acc, y| {
            (0..w).fold(0, |mut w_acc, x| {
                w_acc += directions.iter().fold(0, |acc, (del_x, del_y)| {

                    let mut match_count = 0;
                    let (mut i, mut j) = (x, y);
                    while i > -1 && i < w && j > -1 && j < h && match_count < word_vec.len() && char_at(i, j) == word_vec[match_count] {
                        match_count += 1;
                        i += del_x;
                        j += del_y;
                    }

                    match match_count == word.len() {
                        true => acc + 1,
                        false => acc,
                    }
                });
                w_acc
            }) + h_acc
        }))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let grid = input.lines().map(|l| l.chars().collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();
        let w = grid.first().expect("invalid input").len() as isize;
        let h = grid.len() as isize;

        if h < 3 || w < 3 {
            return Ok(0);
        }

        let char_at = |x: isize, y: isize| grid[y as usize][x as usize];

        Ok((1..h - 1).fold(0, |h_acc, y| {
            (1..w - 1).fold(0, |w_acc, x| {
                match char_at(x, y) == 'A' && (char_at(x - 1, y - 1) == 'M' && char_at(x + 1, y + 1) == 'S' || char_at(x - 1, y - 1) == 'S' && char_at(x + 1, y + 1) == 'M') && (char_at(x - 1, y + 1) == 'M' && char_at(x + 1, y - 1) == 'S' || char_at(x - 1, y + 1) == 'S' && char_at(x + 1, y - 1) == 'M') {
                    true => w_acc + 1,
                    false => w_acc,
                }
            }) + h_acc
        }))

    }
}

pub struct Day5;


impl Solution for Day5 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let invalid = "invalid input";
        let (rules, updates) = input.split_once("\n\n").expect(invalid);
        let rulebook = rules.lines().fold(HashMap::new(), |mut acc, l| {
            let (before, after) = l.split_once("|").expect(invalid);
            let parse = |s: &str| s.parse::<usize>().expect(invalid);
            let (before, after) = (parse(before), parse(after));
            acc.entry((before, after)).or_insert(true);
            acc.entry((after, before)).or_insert(false);
            acc
        });

        Ok(updates.lines().fold(0, |acc, l| {
            let line = l.split(",").map(|v| v.parse::<usize>().expect(invalid)).collect::<Vec<usize>>();
            if line.len() < 2 {
                return acc + 1;
            }

            for i in 0..line.len() - 1 {
                for j in i + 1..line.len() {
                    if let Some(valid) = rulebook.get(&(line[i], line[j])) {
                        if !valid { return acc; }
                    }
                }
            }

            acc + line[line.len() / 2]
        }))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let invalid = "invalid input";
        let (rules, updates) = input.split_once("\n\n").expect(invalid);
        let rulebook = rules.lines().fold(HashMap::new(), |mut acc, l| {
            let (before, after) = l.split_once("|").expect(invalid);
            let parse = |s: &str| s.parse::<usize>().expect(invalid);
            let (before, after) = (parse(before), parse(after));
            acc.entry((before, after)).or_insert(true);
            acc.entry((after, before)).or_insert(false);
            acc
        });

        Ok(updates.lines().fold(0, |acc, l| {
            let mut line = l.split(",").map(|v| v.parse::<usize>().expect(invalid)).collect::<Vec<usize>>();
            if line.len() < 2 {
                return acc + 1;
            }

            for i in 0..line.len() - 1 {
                for j in i + 1..line.len() {
                    if let Some(valid) = rulebook.get(&(line[i], line[j])) {
                        if !valid {
                            // process invalid line
                            line.sort_by(|&left, &right| {
                                rulebook.get(&(left, right)).map(|&valid| {
                                    match valid {
                                        true => std::cmp::Ordering::Less,
                                        false => std::cmp::Ordering::Greater,
                                    }
                                }).unwrap_or(std::cmp::Ordering::Equal)
                            });

                            return acc + line[line.len() / 2]
                        }
                    }
                }
            }

            acc
        }))
    }
}

pub struct Day6;

impl Solution for Day6 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let ((mut x, mut y), map) = {
            let mut start = None;
            let map = input.lines().enumerate().map(|(y, l)| l.chars().enumerate().inspect(|&(x, c)| {
                if c == '^' || c == '>' || c == 'v' || c == '<' { start = Some((x, y)) }
            }).map(|t| t.1).collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();

            match start {
                None => return Err(Error::InvalidInput("Initial position of guard cannot be determined".into())),
                Some((x, y)) => ((x as isize, y as isize), map),
            }
        };

        let h = map.len() as isize;
        let w = map[0].len() as isize;

        let char_at = |x: isize, y: isize| map[y as usize][x as usize];

        let (mut del_x, mut del_y) = match char_at(x, y) {
            '^' => (0, -1),
            '>' => (1, 0),
            'v' => (0, 1),
            '<' => (-1, 0),
            _ => unreachable!(),
        };

        let mut set = HashSet::new();
        loop {
            set.insert((x, y));

            let (new_x, new_y) = (x + del_x, y + del_y);
            if new_x < 0 || new_x == w || new_y < 0 || new_y == h {
                break;
            }

            if char_at(x + del_x, y + del_y) == '#' {
                (del_x, del_y) = (-del_y, del_x);
            }

            x += del_x;
            y += del_y;
        }

        Ok(set.len())
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let (start , mut map) = {
            let mut start = None;
            let map = input.lines().enumerate().map(|(y, l)| l.chars().enumerate().inspect(|&(x, c)| {
                if c == '^' || c == '>' || c == 'v' || c == '<' { start = Some((x, y)) }
            }).map(|t| t.1).collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();

            match start {
                None => return Err(Error::InvalidInput("Initial position of guard cannot be determined".into())),
                Some((x, y)) => ((x as isize, y as isize), map),
            }
        };

        let h = map.len() as isize;
        let w = map[0].len() as isize;

        let del = match map[start.1 as usize][start.0 as usize] {
            '^' => (0, -1),
            '>' => (1, 0),
            'v' => (0, 1),
            '<' => (-1, 0),
            _ => unreachable!(),
        };

        Ok((0..h).fold(0, |h_acc, oy| {
            (0..w).fold(0, |mut w_acc, ox| {
                if map[oy as usize][ox as usize] == '.' {
                    // create obstacle
                    map[oy as usize][ox as usize] = '#';

                    let mut set = HashSet::new();
                    let (mut x, mut y) = start;
                    let (mut del_x, mut del_y) = del;
                    w_acc += match loop {
                        set.insert((x, y, del_x, del_y));

                        let (new_x, new_y) = (x + del_x, y + del_y);
                        if !(0..w).contains(&new_x) || !(0..h).contains(&new_y) {
                            break false; // out of bounds
                        }

                        if map[new_y as usize][new_x as usize] == '#' {
                            (del_x, del_y) = (-del_y, del_x);
                        }
                        else {
                            x += del_x;
                            y += del_y;
                        }

                        if set.contains(&(x, y, del_x, del_y)) {
                            break true; // found loop
                        }
                    } {
                        true => 1,
                        false => 0,
                    };

                    // remove obstacle
                    map[oy as usize][ox as usize] = '.';
                }

                w_acc
            }) + h_acc
        }))
    }
}

pub struct Day7;

impl Solution for Day7 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let error_str = "Invalid input";
        Ok(input.lines().fold(0, |acc, l| {
            let (test_str, numbers_str) = l.split_once(":").expect(error_str);
            let test = test_str.parse::<usize>().expect(error_str);
            let numbers = numbers_str.split_whitespace().map(|num_str| num_str.parse::<usize>().expect(error_str)).collect::<Vec<usize>>();
            match Self::calibrated(test, &numbers) {
                true => acc + test,
                false => acc,
            }
        }))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let error_str = "Invalid input";
        Ok(input.lines().fold(0, |acc, l| {
            let (test_str, numbers_str) = l.split_once(":").expect(error_str);
            let test = test_str.parse::<usize>().expect(error_str);
            let numbers = numbers_str.split_whitespace().map(|num_str| num_str.parse::<usize>().expect(error_str)).collect::<Vec<usize>>();
            match Self::concatenated_calibration(test, &numbers) {
                true => acc + test,
                false => acc,
            }
        }))
    }
}

impl Day7 {
    fn calibrated(target: usize, numbers: &[usize]) -> bool {
        if numbers.len() == 1 { target == numbers[0] }
        else if target % numbers[numbers.len() - 1] == 0 && Self::calibrated(target / numbers[numbers.len() - 1], &numbers[..numbers.len() - 1]) || target > numbers[numbers.len() - 1] && Self::calibrated(target - numbers[numbers.len() - 1], &numbers[..numbers.len() - 1]) { true }
        else { false }
    }

    fn concatenated_calibration(target: usize, numbers: &[usize]) -> bool {
        if numbers.len() == 1 { return target == numbers[0]; }
        let last = numbers[numbers.len() - 1];
        let remaining_numbers = &numbers[..numbers.len() - 1];
        if target % last == 0 && Self::concatenated_calibration(target / last, remaining_numbers) || target > last && Self::concatenated_calibration(target - last, remaining_numbers) { return true; }
        let last_digit_count = last.ilog10();
        let e = 10usize.pow(last_digit_count as u32 + 1);
        if target.ilog10() > last_digit_count && target % e == last && Self::concatenated_calibration(target / e, remaining_numbers) { return true; }
        false
    }
}
