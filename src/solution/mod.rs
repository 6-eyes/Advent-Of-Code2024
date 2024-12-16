use super::{Solution, Error};
use std::{cmp::Reverse, collections::{BinaryHeap, HashMap, HashSet, VecDeque}};

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
        else { target % numbers[numbers.len() - 1] == 0 && Self::calibrated(target / numbers[numbers.len() - 1], &numbers[..numbers.len() - 1]) || target > numbers[numbers.len() - 1] && Self::calibrated(target - numbers[numbers.len() - 1], &numbers[..numbers.len() - 1]) }
    }

    fn concatenated_calibration(target: usize, numbers: &[usize]) -> bool {
        if numbers.len() == 1 { return target == numbers[0]; }
        let last = numbers[numbers.len() - 1];
        let remaining_numbers = &numbers[..numbers.len() - 1];
        if target % last == 0 && Self::concatenated_calibration(target / last, remaining_numbers) || target > last && Self::concatenated_calibration(target - last, remaining_numbers) { return true; }
        let last_digit_count = last.ilog10();
        let e = 10usize.pow(last_digit_count + 1);
        if target.ilog10() > last_digit_count && target % e == last && Self::concatenated_calibration(target / e, remaining_numbers) { return true; }
        false
    }
}

pub struct Day8;

impl Solution for Day8 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let (antennas, w, h) = {
            let mut h = None;
            let mut w = None;
            let antennas = input.lines().enumerate().fold(HashMap::<char, Vec<(usize, usize)>>::new(), |mut acc, (y, l)| {
                if w.is_none() { w = Some(l.len()); };
                if h.is_none() || h.unwrap() < y { h = Some(y); }

                l.chars().enumerate().filter(|(_, c)| c.is_alphanumeric()).for_each(|(x, c)| {
                    acc.entry(c).and_modify(|v| v.push((x, y))).or_insert(vec!{ (x, y) });
                });
                acc
            });
            
            if h.is_none() || w.is_none() || antennas.is_empty() { return Err(Error::InvalidInput("invalid input".into())) }
            (antennas, w.unwrap() as isize, h.unwrap() as isize + 1)
        };

        Ok(antennas.values().fold(HashSet::new(), |mut acc, antennas| {
            antennas.iter().flat_map(|&left| {
                antennas.iter().filter_map(move |&right| match left == right {
                    true => None,
                    false => Some((left, right)),
                })
            }).for_each(|(left, right)| {
                let antinode = (2 * left.0 as isize - right.0 as isize, 2 * left.1 as isize - right.1 as isize);
                if (0..h).contains(&antinode.1) && (0..w).contains(&antinode.0) {
                    acc.insert(antinode);
                }
            });

            acc
        }).len())
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let (antennas, w, h) = {
            let mut h = None;
            let mut w = None;
            let antennas = input.lines().enumerate().fold(HashMap::<char, Vec<(usize, usize)>>::new(), |mut acc, (y, l)| {
                if w.is_none() { w = Some(l.len()); };
                if h.is_none() || h.unwrap() < y { h = Some(y); }

                l.chars().enumerate().filter(|(_, c)| c.is_alphanumeric()).for_each(|(x, c)| {
                    acc.entry(c).and_modify(|v| v.push((x, y))).or_insert(vec!{ (x, y) });
                });
                acc
            });
            
            if h.is_none() || w.is_none() || antennas.is_empty() { return Err(Error::InvalidInput("invalid input".into())) }
            (antennas, w.unwrap() as isize, h.unwrap() as isize + 1)
        };

        // initialize the antinodes with antennas
        let antinodes = antennas.values().flatten().map(|&v| (v.0 as isize, v.1 as isize)).collect::<HashSet<(isize, isize)>>();

        Ok(antennas.values().fold(antinodes, |mut acc, antennas| {
            antennas.iter().flat_map(|&left| {
                antennas.iter().filter_map(move |&right| match left == right {
                    true => None,
                    false => Some((left, right)),
                })
            }).for_each(|(left, right)| {
                let mut antinode = (left.0 as isize, left.1 as isize);
                let del = (right.0 as isize - antinode.0, right.1 as isize - antinode.1);
                loop {
                    antinode = (antinode.0 - del.0, antinode.1 - del.1);
                    match (0..h).contains(&antinode.1) && (0..w).contains(&antinode.0) {
                            true => { acc.insert(antinode); },
                            false => break,
                    }
                }
            });

            acc
        }).len())
    }
}

pub struct Day9;

impl Solution for Day9 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let mut id = 0;
        let mut disk = input.lines().flat_map(&str::chars).enumerate().flat_map(|(i, c)| {
            if let Some(count) = c.to_digit(10) {
                match i & 1 {
                    0 => {
                        let iter = std::iter::repeat_n(Some(id), count as usize);
                        id += 1;
                        iter
                    },
                    1 => std::iter::repeat_n(None, count as usize),
                    _ => unreachable!(),
                }
            }
            else {
                std::iter::repeat_n(None, 0)
            }
        }).collect::<Vec<Option<usize>>>();

        if disk.is_empty() { return Ok(0) }

        let mut s = 0;
        let mut e = disk.len() - 1;

        while s < e {
            while disk[s].is_some() { s += 1; }
            while disk[e].is_none() { e -= 1; disk.pop(); }

            disk[s] = disk.pop().unwrap();
            e -= 1;
            s += 1;
        }

        Ok(disk.into_iter().flatten().enumerate().fold(0, |acc, (i, v)| i * v + acc))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let err_msg = "invalid input";
        let (mut files, mut spaces, mut fid, _) = input.lines().flat_map(&str::chars).enumerate().fold((HashMap::new(), Vec::new(), 0usize, 0), |(mut files, mut spaces, fid, pos), (i, c)| {
            let count = c.to_digit(10).expect(err_msg) as usize;
            match i & 1 {
                0 if count != 0 => {
                    files.insert(fid, (pos, count));
                    (files, spaces, fid + 1, pos + count)
                },
                1 => {
                    if count != 0 { spaces.push((pos, count)); }
                    (files, spaces, fid, pos + count)
                },
                _ => unreachable!(),
            }
        });

        while fid > 0 {
            fid -= 1;
            let (file_pos, file_len) = files[&fid];

            let take_till = spaces.iter().take_while(|&&(space_pos, _)| space_pos < file_pos).count();
            spaces.truncate(take_till);

            if let Some((idx, &(pos, len))) = spaces.iter().enumerate().find(|(_, &(_, space_len))| space_len >= file_len) {
                match len == file_len {
                    true => { spaces.remove(idx); },
                    false => { spaces[idx] = (pos + file_len, len - file_len); }
                }
                files.entry(fid).and_modify(|v| *v = (pos, file_len));
            }
        }

        Ok(files.into_iter().map(|(k, v)| k * v.1 * (2 * v.0 + v.1 - 1) / 2).sum::<usize>())
    }
}

pub struct Day10;

impl Solution for Day10 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let (mut trailheads, grid) = input.lines().enumerate().fold((Vec::new(), Vec::new()), |(mut trailheads, mut grid), (y, l)| {
            grid.push(l.chars().enumerate().map(|(x, c)| {
                let c = c.to_digit(10).expect("invalid input");
                if c == 0 { trailheads.push((x as isize, y as isize)); }
                c
            }).collect::<Vec<u32>>());

            (trailheads, grid)
        });

        let val_at = |x: isize, y: isize| grid[y as usize][x as usize];

        let h = grid.len() as isize;
        let w = grid.first().expect("empty input").len() as isize;

        let mut score = 0;
        while let Some(trail) = trailheads.pop() {
            let mut q = VecDeque::new();
            q.push_back(trail);

            let mut seen = HashSet::new();
            seen.insert(trail);

            while let Some((x, y)) = q.pop_front() {
                let current = val_at(x, y);
                [(x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1)].into_iter().for_each(|(i, j)| {
                    if i >= 0 && i < w && j >= 0 && j < h && val_at(i, j) == current + 1 && !seen.contains(&(i, j)) {
                        seen.insert((i, j));
                        match val_at(i, j) == 9 {
                            true => score += 1,
                            false => q.push_back((i, j)),
                        }
                    }
                });
            }

        }

        Ok(score)
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let (mut trailheads, grid) = input.lines().enumerate().fold((VecDeque::new(), Vec::new()), |(mut trailheads, mut grid), (y, l)| {
            grid.push(l.chars().enumerate().map(|(x, c)| {
                let c = c.to_digit(10).expect("invalid input");
                if c == 0 { trailheads.push_back((x as isize, y as isize)); }
                c
            }).collect::<Vec<u32>>());

            (trailheads, grid)
        });

        let val_at = |x: isize, y: isize| grid[y as usize][x as usize];

        let h = grid.len() as isize;
        let w = grid.first().expect("empty input").len() as isize;

        let mut score = 0;
        while let Some((x, y)) = trailheads.pop_front() {
            let current = val_at(x, y);
            [(x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1)].into_iter().filter(|&(i, j)| i >= 0 && i < w && j >= 0 && j < h && val_at(i, j) == current + 1).for_each(|(i, j)| {
                match val_at(i, j) == 9 {
                    true => score += 1,
                    false => trailheads.push_back((i, j)),
                }
            });
        }

        Ok(score)
    }
}

pub struct Day11;

impl Solution for Day11 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let init_stones = input.split_whitespace().map(|v| v.parse::<usize>().expect("invalid input")).collect::<Vec<usize>>();
        let blinks = 25;
        
        Ok(Self::count(&init_stones, blinks, &mut HashMap::new()))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let init_stones = input.split_whitespace().map(|v| v.parse::<usize>().expect("invalid input")).collect::<Vec<usize>>();
        let blinks = 75;
        
        Ok(Self::count(&init_stones, blinks, &mut HashMap::new()))
    }
}

impl Day11 {
    fn count(stones: &[usize], remaining_blinks: u16, cache: &mut HashMap<(Vec<usize>, u16), usize>) -> usize {
        if let Some(&count) = cache.get(&(stones.to_vec(), remaining_blinks)) { count }
        else if remaining_blinks == 0 { stones.len() }
        else {
            let total = stones.iter().map(|&stone| Self::count(&Self::split_stone(stone), remaining_blinks - 1, cache)).sum::<usize>();
            cache.insert((stones.to_vec(), remaining_blinks), total);
            total
        }
    }

    fn split_stone(stone: usize) -> Vec<usize> {
        match stone == 0 {
            true => vec!{ 1 },
            false => {
                let digits = stone.ilog10();
                match digits & 1 == 1 {
                    true => {
                        let radix = 10usize.pow((digits  + 1) / 2);
                        vec!{ stone / radix, stone % radix }
                    },
                    false => vec!{ stone * 2024 },
                }
            },
        }
    }
}

pub struct Day12;

impl Solution for Day12 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let region = input.lines().map(|l| l.chars().collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();
        let char_at = |x: isize, y: isize| region[y as usize][x as usize];

        let h = region.len() as isize;
        let w = region.first().ok_or(Error::InvalidInput("no input provided".into()))?.len() as isize;

        let plots = region.iter().enumerate().fold((Vec::new(), HashSet::new()), |(mut plots, mut seen), (y, l)| {
            l.iter().enumerate().for_each(|(x, &c)| {
                let (x, y) = (x as isize, y as isize);
                if seen.contains(&(x, y)) { return; } 

                seen.insert((x, y));

                let mut q = VecDeque::new();
                q.push_back((x, y));

                let mut plot = HashSet::new();
                plot.insert((x, y));

                while let Some((i, j)) = q.pop_front() {
                    [(i + 1, j), (i, j + 1), (i - 1, j), (i, j - 1)].into_iter().filter(|&(new_i, new_j)| new_i >= 0 && new_i < w && new_j >= 0 && new_j < h && c == char_at(new_i, new_j)).for_each(|coor| {
                        if !plot.contains(&coor) {
                            plot.insert(coor);
                            q.push_back(coor);
                        }
                    });
                }

                seen.extend(plot.clone());
                plots.push(plot);
            });
            (plots, seen)
        }).0;

        Ok(plots.into_iter().map(|plot| {
            let area = plot.len();
            area * plot.iter().fold(area * 4, |acc, &(x, y)| acc - [(x + 1, y), (x, y + 1), (x - 1, y), (x, y - 1)].into_iter().filter(|coor| plot.contains(coor)).count())
        }).sum::<usize>())
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let region = input.lines().map(|l| l.chars().collect::<Vec<char>>()).collect::<Vec<Vec<char>>>();
        let char_at = |x: isize, y: isize| region[y as usize][x as usize];

        let h = region.len() as isize;
        let w = region.first().ok_or(Error::InvalidInput("no input provided".into()))?.len() as isize;

        let plots = region.iter().enumerate().fold((Vec::new(), HashSet::new()), |(mut plots, mut seen), (y, l)| {
            l.iter().enumerate().for_each(|(x, &c)| {
                let (x, y) = (x as isize, y as isize);
                if seen.contains(&(x, y)) { return; } 

                seen.insert((x, y));

                let mut q = VecDeque::new();
                q.push_back((x, y));

                let mut plot = HashSet::new();
                plot.insert((x, y));

                while let Some((i, j)) = q.pop_front() {
                    [(i + 1, j), (i, j + 1), (i - 1, j), (i, j - 1)].into_iter().filter(|&(new_i, new_j)| new_i >= 0 && new_i < w && new_j >= 0 && new_j < h && c == char_at(new_i, new_j)).for_each(|coor| {
                        if !plot.contains(&coor) {
                            plot.insert(coor);
                            q.push_back(coor);
                        }
                    });
                }

                seen.extend(plot.clone());
                plots.push(plot);
            });
            (plots, seen)
        }).0;

        Ok(plots.into_iter().map(|plot| {
            plot.len() * plot.into_iter().fold(HashMap::new(), |mut acc: HashMap<(isize, isize), Vec<(isize, isize)>>, (x, y)| {
                let (x, y) = (2 * x, 2 * y);
                [(x + 1, y + 1), (x - 1, y + 1), (x - 1, y - 1), (x + 1, y - 1)].into_iter().for_each(|(i, j)| {
                    acc.entry((i, j)).and_modify(|added_by| added_by.push((x, y))).or_insert(vec!{ (x, y) });
                });
                acc
            }).values().map(|v| match v.len() {
                    2 if v[0].0.abs_diff(v[1].0) == v[0].1.abs_diff(v[1].1) => 2,
                    1 | 3 => 1,
                    _ => 0,
            }).sum::<usize>()
        }).sum::<usize>())
    }
}

pub struct Day13;

impl Solution for Day13 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        Ok(Self::win_prize(input, 0))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        Ok(Self::win_prize(input, 10000000000000))
    }
}

impl Day13 {
    fn win_prize(input: String, offset: usize) -> usize {
        let error_msg = "invalid input";
        let extract_coordinate = |l: &str| {
            let s = l.split_once(',').expect(error_msg);
            let extract_num = |l: &str| l.chars().skip_while(|c| !c.is_ascii_digit()).collect::<String>().parse::<usize>().expect(error_msg);
            (extract_num(s.0), extract_num(s.1))
        };

        input.split("\n\n").map(|machine_str| {
            let machine = machine_str.lines().map(extract_coordinate).collect::<Vec<(usize, usize)>>();
            let a = machine[0];
            let b = machine[1];
            let x = (machine[2].0 + offset, machine[2].1 + offset);

            let checked_sub = |a: usize, b: usize| a.abs_diff(b);
            let denom = checked_sub(a.1 * b.0, a.0 * b.1);
            let num_b = checked_sub(a.1 * x.0, a.0 * x.1);
            let num_a = checked_sub(b.0 * x.1, b.1 * x.0);

            let checked_div = |n: usize, d: usize| match n.checked_rem(d)? {
                0 => Some(n / d),
                _ => None,
            };
            checked_div(num_b, denom).and_then(|token_b| checked_div(num_a, denom).map(|token_a| token_a * 3 + token_b)).unwrap_or(0)
        }).sum::<usize>()
    }
}

pub struct Day14;

impl Solution for Day14 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let error_msg = "invalid input";
        let w = 101; // 11 for test
        let h = 103; // 7 for test
        let (w_half, h_half) = (w / 2, h / 2);
        let seconds = 100;

        Ok(input.lines().fold(&mut [0; 4], |acc, l| {
            let mut line_iter = l.split_whitespace().map(|s: &str| {
                let (_, coor_str) = s.split_once('=').expect(error_msg);
                let (x, y) = coor_str.split_once(',').expect(error_msg);
                let parse = |s: &str| s.parse::<isize>().expect(error_msg);
                (parse(x), parse(y))
            });

            let p = line_iter.next().expect(error_msg);
            let v = line_iter.next().expect(error_msg);

            let confine = |x, v, l| ((x + seconds * v) % l + l) % l;
            let (x, y) = (confine(p.0, v.0, w), confine(p.1, v.1, h));

            if x < w_half && y < h_half { acc[0] += 1; }
            else if x > w_half && y < h_half { acc[1] += 1; }
            else if x < w_half && y > h_half { acc[2] += 1; }
            else if x > w_half && y > h_half { acc[3] += 1; }
            acc
        }).iter_mut().fold(1, |acc, v| acc * *v))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let error_msg = "invalid input";
        let w = 101; // 11 for test
        let h = 103; // 7 for test

        let mut input = input.lines().map(|l| {
            let mut line_iter = l.split_whitespace().map(|s: &str| {
                let (_, coor_str) = s.split_once('=').expect(error_msg);
                let (x, y) = coor_str.split_once(',').expect(error_msg);
                let parse = |s: &str| s.parse::<isize>().expect(error_msg);
                (parse(x), parse(y))
            });

            (line_iter.next().expect(error_msg), line_iter.next().expect(error_msg))
        }).collect::<Vec<((isize, isize), (isize, isize))>>();

        let mut second = 0;
        Ok(loop {
            second += 1;
            let unique_positions = input.iter_mut().fold(HashSet::new(), |mut acc, (p, v)| {
                let m = |x, v, l| ((x + v) % l + l) % l;
                *p = (m(p.0, v.0, w), m(p.1, v.1, h));

                acc.insert(*p);
                acc
            });

            if unique_positions.len() == input.len() {
                // print tree
                // let mut map = vec!{ vec!{ '.'; h as usize }; w as usize };
                // input.iter().for_each(|(p, _)| map[p.0 as usize][p.1 as usize] = '#');
                // map.into_iter().for_each(|l| println!("{}", l.into_iter().collect::<String>()));
                break second;
            }
        })
    }
}

pub struct Day15;

impl Solution for Day15 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let error_msg = "invalid input";
        let (grid, moves) = input.split_once("\n\n").expect(error_msg);

        let (walls, mut boxes, robot) = grid.lines().enumerate().fold((HashSet::new(), HashSet::new(), None), |(mut walls, mut boxes, mut robot), (y, l)| {
            l.chars().enumerate().for_each(|(x, c)| {
                let (x, y) = (x as isize, y as isize);
                match c {
                    '#' => { walls.insert((x, y)); },
                    'O' => { boxes.insert((x, y)); },
                    '@' if robot.is_none() => robot = Some((x, y)),
                    '.' => (),
                    _ => panic!("invalid input {}", c),
                }
            });
            (walls, boxes, robot)
        });

        let mut robot = robot.expect(error_msg);

        moves.lines().flat_map(&str::chars).map(|c| {
            match c {
                '<' => (-1, 0),
                '^' => (0, -1),
                '>' => (1, 0),
                'v' => (0, 1),
                _ => panic!("invalid input {}", c),
            }
        }).for_each(|m| {
            let pos = (robot.0 + m.0, robot.1 + m.1);
            if boxes.contains(&pos) {
                let mut n = pos;
                if loop {
                    n = (n.0 + m.0, n.1 + m.1);
                    if walls.contains(&n) { break false; }
                    else if !boxes.contains(&n) { break true; }
                } {
                    boxes.insert(n);
                    boxes.remove(&pos);

                    robot = pos;
                }
            }
            else if !walls.contains(&pos) {
                robot = pos;
            }
        });

        Ok(boxes.into_iter().map(|(x, y)| (y * 100 + x) as usize).sum::<usize>())
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let error_msg = "invalid input";
        let (grid, moves) = input.split_once("\n\n").expect(error_msg);

        let (walls, mut boxes, robot) = grid.lines().enumerate().fold((HashSet::new(), HashSet::new(), None), |(mut walls, mut boxes, mut robot), (y, l)| {
            l.chars().enumerate().for_each(|(x, c)| {
                let (x, y) = (2 * x as isize, y as isize);
                match c {
                    '#' => { walls.insert((x, y)); },
                    'O' => { boxes.insert((x, y)); },
                    '@' if robot.is_none() => robot = Some((x, y)),
                    '.' => (),
                    _ => panic!("invalid input {}", c),
                }
            });
            (walls, boxes, robot)
        });

        let mut robot = robot.expect(error_msg);

        moves.lines().flat_map(&str::chars).map(|c| {
            match c {
                '<' => (-1, 0),
                '^' => (0, -1),
                '>' => (1, 0),
                'v' => (0, 1),
                _ => panic!("invalid input {}", c),
            }
        }).for_each(|m| {
            if m.0 == 0 {
                let mut boxes_to_move = Vec::new();

                let get_boxes_on_next_step = |last_row: Option<&HashSet<(isize, isize)>>| {
                    let mut b = HashSet::new();
                    match last_row {
                        None => {
                            for d in [-1, 0] {
                                let pos = (robot.0 + d, robot.1 + m.1);
                                if walls.contains(&pos) { return None; }
                                else if boxes.contains(&pos) { b.insert(pos); }
                            }
                        },
                        Some(last_row) => {
                            for &pos in last_row {
                                for d in [-1, 0, 1] {
                                    let pos = (pos.0 + d, pos.1 + m.1);
                                    if walls.contains(&pos) { return None; }
                                    else if boxes.contains(&pos) { b.insert(pos); }
                                }
                            }
                        }
                    }
                    Some(b)
                };

                if loop {
                    match get_boxes_on_next_step(boxes_to_move.last()) {
                        None => break false,
                        Some(level) if level.is_empty() => break true,
                        Some(level) => boxes_to_move.push(level),
                    };
                } {
                    while let Some(level) = boxes_to_move.pop() {
                        level.into_iter().for_each(|b| {
                            boxes.remove(&b);
                            boxes.insert((b.0, b.1 + m.1));
                        });
                    }
                    robot.1 += m.1;
                }
            }
            else if m.1 == 0 {
                let initial_p = if m.0 == 1 { (robot.0 + 1, robot.1) } else { (robot.0 - 2, robot.1) };
                let mut p = initial_p;
                if loop {
                    if walls.contains(&p) { break false; }
                    if !boxes.contains(&p) { break true; }
                    p.0 += m.0 * 2;
                } {
                    while p != initial_p {
                        p.0 -= m.0 * 2;
                        boxes.remove(&p);
                        boxes.insert((p.0 + m.0, p.1));
                    }
                    robot.0 += m.0;
                }
            }
        });

        Ok(boxes.into_iter().map(|(x, y)| (y * 100 + x) as usize).sum::<usize>())
    }
}

pub struct Day16;

impl Solution for Day16 {
    fn part_1(&self, input: String) -> Result<usize, Error> {
        let (walls, s, e) = {
            let (walls, s, e) = input.lines().enumerate().fold((HashSet::new(), None, None), |(mut walls, mut start, mut end), (y, l)| {
                l.chars().enumerate().for_each(|(x, c)| {
                    let (x, y) = (x as isize, y as isize);
                    match c {
                        '#' => { walls.insert((x, y)); },
                        'S' if start.is_none() => start = Some((x, y)),
                        'E' if end.is_none() => end = Some((x, y)),
                        '.' => (),
                        _ => panic!("invalid input {}", c),
                    }
                });
                (walls, start, end)
            });

            (walls, s.expect("start position cannot be determined"), e.expect("end position cannot be determined"))
        };

        let mut nodes = BinaryHeap::new();
        nodes.push(Reverse((0, s, (1, 0))));

        let mut seen = HashSet::new();

        let mut total = None;
        while let Some(Reverse((cost, (x, y), (dx, dy)))) = nodes.pop() {
            if e == (x, y) {
                total = Some(cost);
                break;
            }
            seen.insert(((x, y), (dx, dy)));
            [(cost + 1, (x + dx, y + dy), (dx, dy)), (cost + 1000, (x, y), (-dy, dx)), (cost + 1000, (x, y), (dy, -dx))].into_iter().filter(|state| !walls.contains(&state.1) && !seen.contains(&(state.1, state.2))).for_each(|state| nodes.push(Reverse(state)));
        }

        total.ok_or(Error::InvalidInput("cost cannot be determined".into()))
    }

    fn part_2(&self, input: String) -> Result<usize, Error> {
        let (walls, s, e) = {
            let (walls, s, e) = input.lines().enumerate().fold((HashSet::new(), None, None), |(mut walls, mut start, mut end), (y, l)| {
                l.chars().enumerate().for_each(|(x, c)| {
                    let (x, y) = (x as isize, y as isize);
                    match c {
                        '#' => { walls.insert((x, y)); },
                        'S' if start.is_none() => start = Some((x, y)),
                        'E' if end.is_none() => end = Some((x, y)),
                        '.' => (),
                        _ => panic!("invalid input {}", c),
                    }
                });
                (walls, start, end)
            });

            (walls, s.expect("start position cannot be determined"), e.expect("end position cannot be determined"))
        };

        let mut nodes = BinaryHeap::new();
        nodes.push(Reverse((0, s, (1, 0))));

        let mut total = usize::MAX;

        let mut lowest = HashMap::new();
        lowest.insert((s, (1, 0)), 0);

        let mut parents = HashMap::new();
        let mut end_state = HashSet::new();

        while let Some(Reverse((cost, (x, y), (dx, dy)))) = nodes.pop() {
            if e == (x, y) {
                if cost > total { break; }
                total = cost;
                end_state.insert(((x, y), (dx, dy)));
            }

            [(cost + 1, (x + dx, y + dy), (dx, dy)), (cost + 1000, (x, y), (-dy, dx)), (cost + 1000, (x, y), (dy, -dx))].into_iter().filter(|state| !walls.contains(&state.1)).for_each(|(new_cost, new_pos, new_direction)| {
                let lowest_cost = *lowest.get(&(new_pos, new_direction)).unwrap_or(&usize::MAX);
                match new_cost.cmp(&lowest_cost) {
                    std::cmp::Ordering::Greater => (),
                    o => {
                        if let std::cmp::Ordering::Less = o {
                            lowest.insert((new_pos, new_direction), new_cost);
                            parents.insert((new_pos, new_direction), HashSet::new());
                        }
                        parents.get_mut(&(new_pos, new_direction)).unwrap().insert(((x, y), (dx, dy)));
                        nodes.push(Reverse((new_cost, new_pos, new_direction)));
                    },
                }
            });
        }

        let mut backtrack = end_state.iter().copied().collect::<VecDeque<((isize, isize), (isize, isize))>>();
        while let Some(state) = backtrack.pop_back() {
            match parents.get(&state) {
                None => break,
                Some(s) => s.iter().for_each(|&v| if !end_state.contains(&v) {
                    backtrack.push_front(v);
                    end_state.insert(v);
                }),
            }
        }

        Ok(end_state.into_iter().map(|(pos, _)| pos).collect::<HashSet<(isize, isize)>>().len())
    }
}
