use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::{self, BufRead};

#[derive(Debug, PartialEq, PartialOrd, Eq, Ord, Copy, Clone)]
enum SpringStatus {
    Unknown,
    Operational,
    Damaged
}

/// This struct represents a row of springs with known values encoded as a single usize number. 
#[derive(Debug)]
struct SpringRow {
    base: Vec<SpringStatus>,
    validation: Vec<usize>
}

impl SpringRow {
    
    /// Parse from string format.
    /// 
    /// # Arguments
    /// 
    /// * `text` - A string slice matching the format described in the format.
    /// 
    /// # Panics
    /// 
    /// The method will panic if the string does not match the expected format or if there is a usize overflow which will happen 
    /// if there is a damaged spring in the 65th position from the right or earlier.
    /// 
    fn parse(text: &str) -> Self {
        let (springs, validation) = text.split_once(" ").expect("Invalid string!");

        SpringRow {
            base: springs
                .chars()
                .map(|c| {
                    match c {
                        '.' => SpringStatus::Operational,
                        '#' => SpringStatus::Damaged,
                        '?' => SpringStatus::Unknown,
                        _ => panic!("Invalid spring status!")
                    }
                })
                .collect(),
            validation: validation
                .split(",")
                .map(|n| n.parse::<usize>().expect("Invalid validation number!"))
                .collect()
        }

    }

    fn unfold_and_parse(text: &str, unfold: u8) -> Self {
        let (springs, validation) = text.split_once(" ").expect("Invalid string!");
        Self::parse(format!("{} {}", vec![springs; unfold as usize].join("?"), vec![validation; unfold as usize].join(",")).as_str())
    }

    fn count_solutions<'a>(springs: &'a [SpringStatus], validation: &'a [usize], cache: &mut BTreeMap<(&'a [SpringStatus], &'a [usize]), usize>) -> usize {
        // check cache
        if let Some(value) = cache.get(&(springs, validation)) {
            return *value;
        }

        if springs.len() == 0 && validation.len() == 0 { 
            return 1; 
        }

        match springs.first() {
            Some(SpringStatus::Operational) => SpringRow::count_solutions(&springs[1..], validation, cache),
            Some(SpringStatus::Damaged) => {
                if validation.is_empty() 
                    || springs.len() < validation[0] 
                    || springs[..validation[0]].iter().any(|s| *s == SpringStatus::Operational)
                    || (springs.len() > validation[0] && springs[validation[0]] == SpringStatus::Damaged) {
                    0
                } else {
                    if springs.len() > validation[0] { 
                        let value = SpringRow::count_solutions(&springs[validation[0] + 1..], &validation[1..], cache);
                        cache.insert((springs, validation), value);
                        value 
                    } else if validation.len() == 1 { 1 } else { 0 }
                }
            },
            Some(SpringStatus::Unknown) => {
                if validation.is_empty() 
                    || springs.len() < validation[0] 
                    || springs[..validation[0]].iter().any(|s| *s == SpringStatus::Operational)
                    || (springs.len() > validation[0] && springs[validation[0]] == SpringStatus::Damaged) {
                    SpringRow::count_solutions(&springs[1..], validation, cache)
                } else {
                    let value = (if springs.len() > validation[0] { SpringRow::count_solutions(&springs[validation[0] + 1..], &validation[1..], cache) } else if validation.len() == 1 { 1 } else { 0 })
                    + SpringRow::count_solutions(&springs[1..], validation, cache);
                    cache.insert((springs, validation), value);
                    value 
                }
            },
            None => 0
        }
    }

    fn valid_solutions(&self) -> usize {
        let mut cache: BTreeMap<(&[SpringStatus], &[usize]), usize> = BTreeMap::new();
        SpringRow::count_solutions(&self.base, &self.validation, &mut cache)
    }

    fn as_str(&self) -> String {
        self.base.iter().map(|s| match s {
            SpringStatus::Damaged => '#',
            SpringStatus::Unknown => '?',
            SpringStatus::Operational => '.',
        }).collect::<String>()
    }

}

fn main() {
    let path = env::args().nth(1).expect("Missing required parameter path!");

    let spring_rows: Vec<SpringRow> = io::BufReader::new(
        fs::File::open(path).expect("Could not open file!"))
        .lines()
        .map(|line| SpringRow::unfold_and_parse(line.expect("Could not read line!").as_str(), 5))
        //.map(|line| SpringRow::parse(line.expect("Could not read line!").as_str()))
        .collect();

    let valid_solutions: usize = spring_rows
        .iter()
        .map(|sr| sr.valid_solutions())
        .sum::<usize>();

    println!("Total valid solutions: {}", valid_solutions);
        
}

#[cfg(test)]
mod tests {
    use crate::SpringRow;

    #[test]
    fn test_valid_solutions() {
        let springs = SpringRow::parse("# 1");
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::parse("? 1");
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::parse(".# 1");
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::parse("?? 1");
        assert_eq!(springs.valid_solutions(), 2);

        let springs = SpringRow::parse("?.# 1,1");
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::parse("?.# 1,5");
        assert_eq!(springs.valid_solutions(), 0);

        let springs = SpringRow::parse("?.#####. 1,5");
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::parse("?.????#. 1,5");
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::parse("???.### 1,1,3");
        assert_eq!(springs.valid_solutions(), 1);
        
        let springs = SpringRow::unfold_and_parse("???.### 1,1,3", 5);
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::unfold_and_parse(".??..??...?##. 1,1,3", 5);
        assert_eq!(springs.valid_solutions(), 16384);

        let springs = SpringRow::unfold_and_parse("?#?#?#?#?#?#?#? 1,3,1,6", 5);
        assert_eq!(springs.valid_solutions(), 1);

        let springs = SpringRow::unfold_and_parse("????.#...#... 4,1,1", 5);
        assert_eq!(springs.valid_solutions(), 16);

        let springs = SpringRow::unfold_and_parse("????.######..#####. 1,6,5", 5);
        assert_eq!(springs.valid_solutions(), 2500);

        let springs = SpringRow::unfold_and_parse("?###???????? 3,2,1", 5);
        assert_eq!(springs.valid_solutions(), 506250);
    }

}
