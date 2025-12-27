/// Library for parsing and processing date-related expressions.
use {
    chrono::{DateTime, Datelike, Duration, Local, TimeZone, Weekday},
    chronoutil::delta::shift_months_opt,
    parser::Rule,
    pest::{Parser, iterators::Pair},
    thiserror::Error,
};

mod parser {
    use pest_derive::Parser;
    /// A parser for date-related expressions using the `pest` parser library.
    #[derive(Parser)]
    #[grammar = "./grammar.pest"]
    pub(crate) struct DateParser;
}

/// Enum representing errors that can occur while parsing a date.
#[derive(Debug, Error)]
pub enum ParseDateError {
    /// Error variant for failed date parsing. Includes the error message.
    #[error("Failed to parse date: {0}")]
    ParseError(String),
}

/// Parse a string representing a date and return the corresponding `DateTime<Local>`.
///
/// This function takes a date specification string, parses it, and returns the
/// resulting `DateTime<Local>` if successful, or an error if the string cannot be parsed.
///
/// The reference date is automatically assumed to be Local::now().
///
/// # Arguments
/// * `string` - The string to be parsed as a date.
///
/// # Returns
/// * `Result<DateTime<Local>, ParseDateError>` - A `DateTime<Local>` if parsing is successful,
///   or a `ParseDateError` if there was an issue.
pub fn from_string(string: &str) -> Result<DateTime<Local>, ParseDateError> {
    from_string_with_reference(string, Local::now())
}

/// Parse a string representing a date and return the corresponding `DateTime<Local>`.
///
/// This function takes a date specification string, parses it, and returns the
/// resulting `DateTime<Local>` if successful, or an error if the string cannot be parsed.
///
/// You specify a reference date from which to calculate relative dates. This allows for
/// easier testing and better use in multi-timezone setups.
///
/// # Arguments
/// * `string` - The string to be parsed as a date.
/// * `reference_date` - The DateTime representing "now", a moment from which relative dates and times will be calculated.
///
/// # Returns
/// * `Result<DateTime<Local>, ParseDateError>` - A `DateTime<Local>` if parsing is successful,
///   or a `ParseDateError` if there was an issue.
pub fn from_string_with_reference(
    string: &str,
    reference_date: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    use parser::{DateParser, Rule};
    let pairs = DateParser::parse(Rule::date_expression, string)
        .map_err(|e| ParseDateError::ParseError(e.to_string()))?;

    if let Some(pair) = pairs.clone().next() {
        match pair.as_rule() {
            Rule::date_expression => {
                let datetime = process_date_expression(pair, reference_date)?;
                return Ok(datetime);
            }
            _ => {
                return Err(ParseDateError::ParseError(
                    "Unexpected rule encountered".to_string(),
                ));
            }
        }
    }

    Err(ParseDateError::ParseError(
        "No valid date expression found".to_string(),
    ))
}

fn process_date_expression(
    pair: Pair<'_, Rule>,
    datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::relative_date => {
                let parsed = process_relative_date(inner_pair, datetime)?;
                return Ok(parsed);
            }
            Rule::relative_term => {
                let parsed = process_relative_term(inner_pair, datetime)?;
                return Ok(parsed);
            }
            Rule::specific_date_and_time => {
                let parsed = process_specific_date_and_time(inner_pair, datetime)?;
                return Ok(parsed);
            }
            Rule::specific_date => {
                let parsed = process_specific_date(inner_pair, datetime)?;
                return Ok(parsed);
            }
            Rule::specific_time => {
                let parsed = process_specific_time(inner_pair, datetime)?;
                return Ok(parsed);
            }
            Rule::specific_day => {
                if let Some(inner) = inner_pair.into_inner().next() {
                    let parsed = process_specific_day(inner.as_rule(), datetime)?;
                    return Ok(parsed);
                }
            }
            Rule::specific_day_and_time => {
                let parsed = process_specific_day_and_time(inner_pair, datetime)?;
                return Ok(parsed);
            }
            Rule::relative_day_and_specific_time => {
                let parsed = process_relative_day_and_specific_time(inner_pair, datetime)?;
                return Ok(parsed);
            }
            Rule::future_time => {
                let parsed = process_future_time(inner_pair, datetime)?;
                return Ok(parsed);
            }
            _ => {
                return Err(ParseDateError::ParseError(
                    "Unexpected rule encountered in date expression".to_string(),
                ));
            }
        }
    }

    Err(ParseDateError::ParseError(
        "No date expression found".to_string(),
    ))
}

fn process_future_time(
    pair: Pair<'_, Rule>,
    mut datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    let mut duration = 0;
    let mut unit: Option<Rule> = None;

    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::number => {
                duration = inner_pair.as_str().trim().parse::<i32>().map_err(|_| {
                    ParseDateError::ParseError("Invalid duration value".to_string())
                })?;
            }
            Rule::minute_s
            | Rule::hour_s
            | Rule::day_s
            | Rule::week_s
            | Rule::month_s
            | Rule::year_s => {
                unit = Some(inner_pair.as_rule());
            }
            _ => {
                return Err(ParseDateError::ParseError("Unexpected rule".to_string()));
            }
        }
    }

    if let Some(unit) = unit {
        datetime = match unit {
            Rule::minute_s => datetime + Duration::minutes(duration as i64),
            Rule::hour_s => datetime + Duration::hours(duration as i64),
            Rule::day_s => datetime + Duration::days(duration as i64),
            Rule::week_s => datetime + Duration::weeks(duration as i64),
            Rule::month_s => shift_months_opt(datetime, duration).ok_or_else(|| {
                ParseDateError::ParseError("Invalid month adjustment".to_string())
            })?,
            Rule::year_s => datetime
                .with_year(datetime.year() + duration)
                .ok_or_else(|| ParseDateError::ParseError("Invalid year adjustment".to_string()))?,
            _ => {
                return Err(ParseDateError::ParseError("Invalid time unit".to_string()));
            }
        };
        Ok(datetime)
    } else {
        Err(ParseDateError::ParseError(
            "Time unit not provided".to_string(),
        ))
    }
}

fn process_specific_date_and_time(
    pair: Pair<'_, Rule>,
    mut datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::specific_date => {
                datetime = process_specific_date(inner_pair, datetime)?;
            }
            Rule::specific_time => {
                datetime = process_specific_time(inner_pair, datetime)?;
            }
            _ => {
                return Err(ParseDateError::ParseError(format!(
                    "Unexpected rule in specific date and time: {:?}",
                    inner_pair.as_rule()
                )));
            }
        }
    }
    Ok(datetime)
}

fn process_specific_day_and_time(
    pair: Pair<'_, Rule>,
    mut datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::specific_day => {
                if let Some(inner) = inner_pair.clone().into_inner().next() {
                    datetime = process_specific_day(inner.as_rule(), datetime)?;
                } else {
                    return Err(ParseDateError::ParseError(format!(
                        "Invalid day of week rule in specific day and time: {:?}",
                        inner_pair.as_rule()
                    )));
                }
            }
            Rule::specific_time => {
                datetime = process_specific_time(inner_pair, datetime)?;
            }
            _ => {
                return Err(ParseDateError::ParseError(format!(
                    "Unexpected rule in specific day and time: {:?}",
                    inner_pair.as_rule()
                )));
            }
        }
    }
    Ok(datetime)
}

fn process_relative_day_and_specific_time(
    pair: Pair<'_, Rule>,
    mut datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::relative_date => {
                datetime = process_relative_date(inner_pair, datetime)?;
            }
            Rule::relative_term => {
                datetime = process_relative_term(inner_pair, datetime)?;
            }
            Rule::specific_time => {
                datetime = process_specific_time(inner_pair, datetime)?;
            }
            _ => {}
        }
    }
    Ok(datetime)
}

fn process_relative_date(
    pair: Pair<'_, Rule>,
    datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    let inner_pairs: Vec<_> = pair.clone().into_inner().collect();

    if inner_pairs.len() == 2 {
        let first_pair = &inner_pairs[0];
        let second_pair = &inner_pairs[1];

        if first_pair.as_rule() == Rule::next_or_last && second_pair.as_rule() == Rule::specific_day
        {
            let direction = first_pair.clone().into_inner().last().unwrap().as_rule();

            if let Some(inner_pair) = second_pair.clone().into_inner().next() {
                match process_weekday(inner_pair.as_rule()) {
                    Ok(target_weekday) => {
                        return shift_to_weekday(datetime, target_weekday, direction);
                    }
                    Err(e) => {
                        return Err(ParseDateError::ParseError(format!(
                            "Unrecognized relative date: {:?}",
                            e.to_string()
                        )));
                    }
                }
            }

            Err(ParseDateError::ParseError(format!(
                "Unrecognized relative date: {:?}",
                second_pair.to_string()
            )))
        } else {
            Err(ParseDateError::ParseError(
                "Pair did not match expected structure for relative_date.".to_string(),
            ))
        }
    } else {
        Err(ParseDateError::ParseError(
            "Unexpected number of inner pairs in relative_date.".to_string(),
        ))
    }
}

fn process_relative_term(
    pair: Pair<'_, Rule>,
    datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    if let Some(inner_pair) = pair.clone().into_inner().next() {
        match inner_pair.as_rule() {
            Rule::tomorrow => {
                return Ok(datetime + Duration::days(1));
            }
            Rule::today => {
                return Ok(datetime);
            }
            Rule::yesterday => {
                return Ok(datetime - Duration::days(1));
            }
            _ => {
                return Err(ParseDateError::ParseError(format!(
                    "Unexpected relative term: {:?}",
                    pair
                )));
            }
        }
    }

    Err(ParseDateError::ParseError(
        "Invalid relative term".to_string(),
    ))
}

fn process_specific_time(
    pair: Pair<'_, Rule>,
    datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    let mut hour: u32 = 0;
    let mut minute: u32 = 0;
    let mut is_pm = false;

    // Iterate through inner pairs to capture hour, minute, and am_pm
    for inner_pair in pair.into_inner() {
        match inner_pair.as_rule() {
            Rule::hour => {
                hour = inner_pair.as_str().parse::<u32>().map_err(|e| {
                    ParseDateError::ParseError(format!(
                        "Failed to parse hour '{}': {e}",
                        inner_pair.as_str()
                    ))
                })?;

                if hour > 23 {
                    return Err(ParseDateError::ParseError(format!(
                        "Invalid hour: {hour:?}"
                    )));
                }
            }
            Rule::minute => {
                minute = inner_pair.as_str().parse::<u32>().map_err(|e| {
                    ParseDateError::ParseError(format!(
                        "Failed to parse minute '{}': {e}",
                        inner_pair.as_str()
                    ))
                })?;
            }
            Rule::am_pm => {
                if let Some(res) = process_is_pm(inner_pair) {
                    is_pm = res;
                }
            }
            _ => {
                return Err(ParseDateError::ParseError(
                    "Unexpected rule in specific_time".to_string(),
                ));
            }
        }
    }

    if is_pm && hour < 12 {
        hour += 12;
    } else if !is_pm && hour == 12 {
        hour = 0;
    }

    let modified_datetime = change_time(datetime, hour, minute)?;

    Ok(modified_datetime)
}

fn process_specific_date(
    pair: Pair<'_, Rule>,
    datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    let mut year: i32 = 0;
    let mut month: u32 = 0;
    let mut day: u32 = 0;

    // Iterate through inner pairs to capture year, month, day
    for inner_pair in pair.clone().into_inner() {
        match inner_pair.as_rule() {
            Rule::date_sep => {}
            Rule::year => {
                year = inner_pair.as_str().parse::<i32>().map_err(|e| {
                    ParseDateError::ParseError(format!("Failed to parse year: {e}"))
                })?;
            }
            Rule::month => {
                month = inner_pair.as_str().parse::<u32>().map_err(|e| {
                    ParseDateError::ParseError(format!("Failed to parse month: {e}"))
                })?;
            }
            Rule::month_name => {
                month = process_month_name(inner_pair.as_str()).map_err(|e| {
                    ParseDateError::ParseError(format!("Failed to parse month name: {e}"))
                })?;
            }
            Rule::month_short_name => {
                month = process_month_name(inner_pair.as_str()).map_err(|e| {
                    ParseDateError::ParseError(format!("Failed to parse short month: {e}"))
                })?;
            }
            Rule::day => {
                day = inner_pair.as_str().parse::<u32>().map_err(|e| {
                    ParseDateError::ParseError(format!(
                        "Failed to parse day '{}': {e}",
                        inner_pair.as_str()
                    ))
                })?;
            }
            _ => {
                return Err(ParseDateError::ParseError(format!(
                    "Unexpected rule {inner_pair:?} in specific_date"
                )));
            }
        }
    }

    datetime
        .with_year(year)
        .and_then(|dt| dt.with_month(month).and_then(|dt| dt.with_day(day)))
        .ok_or(ParseDateError::ParseError(format!(
            "Invalid date: {pair:?}"
        )))
}

fn process_specific_day(
    rule: Rule,
    datetime: DateTime<Local>,
) -> Result<DateTime<Local>, ParseDateError> {
    let target_weekday = process_weekday(rule)?;
    let current_weekday = datetime.weekday();

    let target_day_num = target_weekday.num_days_from_sunday();
    let current_day_num = current_weekday.num_days_from_sunday();

    let days_difference = if target_day_num >= current_day_num {
        (target_day_num - current_day_num) as i64
    } else {
        -((current_day_num - target_day_num) as i64)
    };

    let target_date = datetime + Duration::days(days_difference);
    Ok(target_date)
}

fn process_month_name(month: &str) -> Result<u32, ParseDateError> {
    let n = month.trim().to_ascii_lowercase();

    Ok(match n.as_str() {
        "jan" | "january" => 1,
        "feb" | "february" => 2,
        "mar" | "march" => 3,
        "apr" | "april" => 4,
        "may" => 5,
        "jun" | "june" => 6,
        "jul" | "july" => 7,
        "aug" | "august" => 8,
        "sep" | "sept" | "september" => 9,
        "oct" | "october" => 10,
        "nov" | "november" => 11,
        "dec" | "december" => 12,
        _ => {
            return Err(ParseDateError::ParseError(format!(
                "Invalid month name: {month:?}"
            )));
        }
    })
}

fn process_weekday(day_of_week: Rule) -> Result<Weekday, ParseDateError> {
    match day_of_week {
        Rule::monday => Ok(Weekday::Mon),
        Rule::tuesday => Ok(Weekday::Tue),
        Rule::wednesday => Ok(Weekday::Wed),
        Rule::thursday => Ok(Weekday::Thu),
        Rule::friday => Ok(Weekday::Fri),
        Rule::saturday => Ok(Weekday::Sat),
        Rule::sunday => Ok(Weekday::Sun),
        _ => Err(ParseDateError::ParseError(format!(
            "Invalid weekday: {:?}",
            day_of_week
        ))),
    }
}

fn change_time(
    datetime: DateTime<Local>,
    hour: u32,
    minute: u32,
) -> Result<DateTime<Local>, ParseDateError> {
    match Local.with_ymd_and_hms(
        datetime.year(),
        datetime.month(),
        datetime.day(),
        hour,
        minute,
        0,
    ) {
        chrono::LocalResult::Single(new_datetime) => Ok(new_datetime),
        chrono::LocalResult::None => Err(ParseDateError::ParseError(
            "Invalid date or time components".to_string(),
        )),
        chrono::LocalResult::Ambiguous(_, _) => Err(ParseDateError::ParseError(
            "Ambiguous date and time".to_string(),
        )),
    }
}

fn shift_to_weekday(
    now: DateTime<Local>,
    target_weekday: Weekday,
    direction: Rule,
) -> Result<DateTime<Local>, ParseDateError> {
    let current_weekday = now.weekday();

    let num_from_curr = current_weekday.num_days_from_sunday() as i32;
    let num_from_target = target_weekday.num_days_from_sunday() as i32;

    let days_difference: i32 = match direction {
        Rule::next => {
            if num_from_target == 0 {
                7 - num_from_curr + 7
            } else {
                7 - num_from_curr + num_from_target
            }
        }

        Rule::last => {
            if num_from_target == 0 {
                -num_from_curr
            } else {
                -num_from_curr - 7 + num_from_target
            }
        }
        Rule::this => {
            let diff = (num_from_target as i64) - (num_from_curr as i64);
            if diff >= 0 {
                diff as i32
            } else {
                (diff + 7) as i32
            }
        }
        _ => {
            return Err(ParseDateError::ParseError(format!(
                "Expected last, this or next, got {:?}",
                direction
            )));
        }
    };

    Ok(now + Duration::days(days_difference as i64))
}

fn process_is_pm(pair: Pair<'_, Rule>) -> Option<bool> {
    if let Some(inner_pair) = pair.into_inner().next() {
        if inner_pair.as_rule() == Rule::pm {
            return Some(true);
        } else if inner_pair.as_rule() == Rule::am {
            return Some(false);
        } else {
            return None;
        }
    }
    None
}

//==============================================================================
// Tests
//==============================================================================

#[cfg(test)]
mod tests {
    use {
        super::{
            ParseDateError,
            parser::{DateParser, Rule},
        },
        anyhow::{Result, anyhow},
        chrono::{Datelike, Duration, Local, TimeZone, Timelike, Weekday},
        pest::Parser,
    };

    fn parse_rule(rule: Rule, input: &str) -> Result<()> {
        DateParser::parse(rule, input)
            .map(|mut pairs| {
                pairs
                    .next()
                    .ok_or_else(|| anyhow!("No pair found for rule"))
            })?
            .map(|_| ())
            .map_err(|e| {
                anyhow!(
                    "Failed to parse input `{}` with rule {:?}: {}",
                    input,
                    rule,
                    e
                )
            })
    }

    #[test]
    fn test_date_expression() -> Result<()> {
        let expressions = [
            "next Monday at 10:30AM",
            "tomorrow",
            "today",
            "yesterday",
            "next Wednesday",
            "Saturday",
            "in 2 weeks",
        ];
        for expr in expressions {
            parse_rule(Rule::date_expression, expr)?;
        }
        Ok(())
    }

    #[test]
    fn test_specific_day() -> Result<()> {
        let days = [
            "Monday",
            "monday",
            "Tuesday",
            "tuesday",
            "Wednesday",
            "wednesday",
            "Thursday",
            "thursday",
            "Friday",
            "friday",
            "Saturday",
            "saturday",
            "Sunday",
            "sunday",
        ];

        for day in days {
            parse_rule(Rule::specific_day, day)?;
        }
        Ok(())
    }

    #[test]
    fn test_specific_time() -> Result<()> {
        let times = ["10:30AM", "10:30am", "01:45PM", "1:45pm"];
        for time in times {
            parse_rule(Rule::specific_time, time)?;
        }
        Ok(())
    }

    #[test]
    fn test_relative_term() -> Result<()> {
        let terms = [
            "Tomorrow",
            "tomorrow",
            "Today",
            "today",
            "Yesterday",
            "yesterday",
        ];
        for term in terms {
            parse_rule(Rule::relative_term, term)?;
        }
        Ok(())
    }

    #[test]
    fn test_relative_date() -> Result<()> {
        let dates = [
            "Next Monday",
            "next Tuesday",
            "Last Friday",
            "last saturday",
        ];
        for date in dates {
            parse_rule(Rule::relative_date, date)?;
        }
        Ok(())
    }

    #[test]
    fn test_relative_day_and_specific_time() -> Result<()> {
        let expressions = ["next Monday at 10:30AM", "yesterday at 5:15pm"];
        for expr in expressions {
            parse_rule(Rule::relative_day_and_specific_time, expr)?;
        }
        Ok(())
    }

    #[test]
    fn test_future_time() -> Result<()> {
        let times = ["in 2 days", "in 3 weeks", "in 1 month", "in 5 years"];
        for time in times {
            parse_rule(Rule::future_time, time)?;
        }
        Ok(())
    }

    #[test]
    fn test_time_unit() -> Result<()> {
        let units = [
            "day", "days", "week", "weeks", "month", "months", "year", "years",
        ];
        for unit in units {
            parse_rule(Rule::time_unit, unit)?;
        }
        Ok(())
    }

    #[test]
    fn test_next_or_last() -> Result<()> {
        let words = ["next", "last", "this", "Next", "Last", "This"];
        for word in words {
            parse_rule(Rule::next_or_last, word)?;
        }
        Ok(())
    }

    #[test]
    fn test_am_pm() -> Result<()> {
        let am_pm_cases = ["AM", "am", "PM", "pm"];
        for case in am_pm_cases {
            parse_rule(Rule::am_pm, case)?;
        }
        Ok(())
    }

    #[test]
    fn test_specific_day_and_time_rules() -> Result<()> {
        let valid_cases = vec![
            "Monday at 10:00 AM",
            "Wednesday at 5:30 PM",
            "Friday at 12:45 PM",
            "Sunday at 5 PM",
        ];

        for case in &valid_cases {
            parse_rule(Rule::specific_day_and_time, case).map_err(|e| {
                anyhow!("Expected specific_day_and_time to parse '{}': {}", case, e)
            })?;
        }

        let invalid_cases = vec![
            "Monday 10:00 AM",
            "at 10:00 AM",
            "Thursday at five PM",
            "Holiday at 10:00 AM",
        ];

        for case in &invalid_cases {
            let result = parse_rule(Rule::specific_day_and_time, case);
            assert!(
                result.is_err(),
                "Unexpectedly parsed invalid input: '{}'",
                case
            );
        }

        Ok(())
    }

    #[test]
    fn test_hour() -> Result<()> {
        let valid_cases = vec!["0", "12", "23", "9", "01"];
        for case in &valid_cases {
            parse_rule(Rule::hour, case)
                .map_err(|e| anyhow!("Failed to parse valid hour '{}': {}", case, e))?;
        }

        let invalid_cases = vec!["-1", "a3", "xx"];
        for case in &invalid_cases {
            assert!(
                parse_rule(Rule::hour, case).is_err(),
                "Parsed invalid hour '{}'",
                case
            );
        }
        Ok(())
    }

    #[test]
    fn test_minute() -> Result<()> {
        let valid_cases = vec!["0", "59", "30", "09"];
        for case in &valid_cases {
            parse_rule(Rule::minute, case)
                .map_err(|e| anyhow!("Failed to parse valid minute '{}': {}", case, e))?;
        }

        let invalid_cases = vec!["a9", "xx"];
        for case in &invalid_cases {
            assert!(
                parse_rule(Rule::minute, case).is_err(),
                "Parsed invalid minute '{}'",
                case
            );
        }
        Ok(())
    }

    #[test]
    fn test_number() -> Result<()> {
        let valid_cases = vec!["1", "10", "999", "42"];
        for case in &valid_cases {
            parse_rule(Rule::number, case)
                .map_err(|e| anyhow!("Failed to parse valid number '{}': {}", case, e))?;
        }

        let invalid_cases = vec!["", "xx"];
        for case in &invalid_cases {
            assert!(
                parse_rule(Rule::number, case).is_err(),
                "Parsed invalid number '{}'",
                case
            );
        }
        Ok(())
    }

    #[test]
    fn test_monday() -> Result<()> {
        let days = vec!["Monday", "monday"];

        for day in days {
            parse_rule(Rule::monday, day)
                .map_err(|e| anyhow!("Failed to parse valid day '{}': {}", day, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_tuesday() -> Result<()> {
        let days = vec!["Tuesday", "tuesday"];

        for day in days {
            parse_rule(Rule::tuesday, day)
                .map_err(|e| anyhow!("Failed to parse valid day '{}': {}", day, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_wednesday() -> Result<()> {
        let days = vec!["Wednesday", "wednesday"];

        for day in days {
            parse_rule(Rule::wednesday, day)
                .map_err(|e| anyhow!("Failed to parse valid day '{}': {}", day, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_thursday() -> Result<()> {
        let days = vec!["Thursday", "thursday"];

        for day in days {
            parse_rule(Rule::thursday, day)
                .map_err(|e| anyhow!("Failed to parse valid day '{}': {}", day, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_friday() -> Result<()> {
        let days = vec!["Friday", "friday"];

        for day in days {
            parse_rule(Rule::friday, day)
                .map_err(|e| anyhow!("Failed to parse valid day '{}': {}", day, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_saturday() -> Result<()> {
        let days = vec!["Saturday", "saturday"];

        for day in days {
            parse_rule(Rule::saturday, day)
                .map_err(|e| anyhow!("Failed to parse valid day '{}': {}", day, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_sunday() -> Result<()> {
        let days = vec!["Sunday", "sunday"];

        for day in days {
            parse_rule(Rule::sunday, day)
                .map_err(|e| anyhow!("Failed to parse valid day '{}': {}", day, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_tomorrow() -> Result<()> {
        let terms = vec!["Tomorrow", "tomorrow"];
        for term in terms {
            parse_rule(Rule::tomorrow, term)
                .map_err(|e| anyhow!("Failed to parse valid relative term '{}': {}", term, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_today() -> Result<()> {
        let terms = vec!["Today", "today"];
        for term in terms {
            parse_rule(Rule::today, term)
                .map_err(|e| anyhow!("Failed to parse valid relative term '{}': {}", term, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_yesterday() -> Result<()> {
        let terms = vec!["Yesterday", "yesterday"];
        for term in terms {
            parse_rule(Rule::yesterday, term)
                .map_err(|e| anyhow!("Failed to parse valid relative term '{}': {}", term, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_next() -> Result<()> {
        let directions = vec!["Next", "next"];
        for direction in directions {
            parse_rule(Rule::next, direction).map_err(|e| {
                anyhow!(
                    "Failed to parse valid relative direction term '{}': {}",
                    direction,
                    e
                )
            })?;
        }
        Ok(())
    }

    #[test]
    fn test_this() -> Result<()> {
        let directions = vec!["This", "this"];
        for direction in directions {
            parse_rule(Rule::this, direction).map_err(|e| {
                anyhow!(
                    "Failed to parse valid relative direction term '{}': {}",
                    direction,
                    e
                )
            })?;
        }
        Ok(())
    }

    #[test]
    fn test_last() -> Result<()> {
        let directions = vec!["Last", "last"];
        for direction in directions {
            parse_rule(Rule::last, direction).map_err(|e| {
                anyhow!(
                    "Failed to parse valid relative direction term '{}': {}",
                    direction,
                    e
                )
            })?;
        }
        Ok(())
    }

    #[test]
    fn test_days() -> Result<()> {
        let units = vec!["day", "days"];
        for unit in units {
            parse_rule(Rule::day_s, unit)
                .map_err(|e| anyhow!("Failed to parse valid time unit '{}': {}", unit, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_weeks() -> Result<()> {
        let units = vec!["week", "weeks"];
        for unit in units {
            parse_rule(Rule::week_s, unit)
                .map_err(|e| anyhow!("Failed to parse valid time unit '{}': {}", unit, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_months() -> Result<()> {
        let units = vec!["month", "months"];
        for unit in units {
            parse_rule(Rule::month_s, unit)
                .map_err(|e| anyhow!("Failed to parse valid time unit '{}': {}", unit, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_years() -> Result<()> {
        let units = vec!["year", "years"];
        for unit in units {
            parse_rule(Rule::year_s, unit)
                .map_err(|e| anyhow!("Failed to parse valid time unit '{}': {}", unit, e))?;
        }
        Ok(())
    }

    #[test]
    fn test_whitespace_empty_output() -> Result<()> {
        let result = DateParser::parse(Rule::WHITESPACE, " ")
            .map_err(|e| anyhow!("Failed to parse ' ' as WHITESPACE: {}", e))?;

        assert!(
            result.clone().next().is_none(),
            "Expected an empty result, but got pairs: {:?}",
            result
        );

        Ok(())
    }

    mod helper_functions {
        use {
            crate::ParseDateError,
            chrono::{DateTime, Datelike, Local, Weekday},
        };

        pub(super) fn assert_weekday_result(
            result: Result<Weekday, ParseDateError>,
            expected: Weekday,
        ) {
            match result {
                Ok(weekday) => assert_eq!(weekday, expected),
                Err(e) => panic!("Expected Ok but got error: {:?}", e),
            }
        }

        pub(super) fn assert_specific_day_result(
            result: Result<DateTime<Local>, ParseDateError>,
            expected_weekday: Weekday,
        ) {
            match result {
                Ok(datetime) => assert_eq!(datetime.weekday(), expected_weekday),
                Err(e) => panic!("Expected Ok but got error: {:?}", e),
            }
        }
    }

    #[cfg(test)]
    mod process_am_pm_tests {
        use {
            crate::parser::{DateParser, Rule},
            pest::Parser,
        };

        #[test]
        fn test_process_am_pm_for_pm() {
            let pair = DateParser::parse(Rule::am_pm, "PM")
                .unwrap()
                .next()
                .unwrap();

            assert_eq!(crate::process_is_pm(pair), Some(true));
        }

        #[test]
        fn test_process_am_pm_for_am() {
            let pair = DateParser::parse(Rule::am_pm, "AM")
                .unwrap()
                .next()
                .unwrap();

            assert_eq!(crate::process_is_pm(pair), Some(false));
        }

        #[test]
        fn test_process_am_pm_for_invalid_input() {
            let pair = DateParser::parse(Rule::date_expression, "today") // Use an appropriate invalid rule or input
                .unwrap()
                .next()
                .unwrap();

            assert_eq!(crate::process_is_pm(pair), None);
        }
    }

    #[cfg(test)]
    mod process_weekday_tests {
        use {
            super::helper_functions::assert_weekday_result,
            crate::{ParseDateError, parser::Rule},
            chrono::Weekday,
        };

        #[test]
        fn test_process_weekday_valid() {
            assert_weekday_result(crate::process_weekday(Rule::monday), Weekday::Mon);
            assert_weekday_result(crate::process_weekday(Rule::tuesday), Weekday::Tue);
            assert_weekday_result(crate::process_weekday(Rule::wednesday), Weekday::Wed);
            assert_weekday_result(crate::process_weekday(Rule::thursday), Weekday::Thu);
            assert_weekday_result(crate::process_weekday(Rule::friday), Weekday::Fri);
            assert_weekday_result(crate::process_weekday(Rule::saturday), Weekday::Sat);
            assert_weekday_result(crate::process_weekday(Rule::sunday), Weekday::Sun);
        }

        #[test]
        fn test_process_weekday_invalid() {
            let invalid_weekday = Rule::EOI;
            let result = crate::process_weekday(invalid_weekday);

            assert!(result.is_err());
            if let Err(ParseDateError::ParseError(msg)) = result {
                assert_ne!(msg, "");
            } else {
                panic!("Expected a message for an error for invalid weekday");
            }
        }
    }

    #[cfg(test)]
    mod process_specific_day_tests {
        use {
            super::helper_functions::assert_specific_day_result,
            crate::{ParseDateError, parser::Rule},
            chrono::{Local, Weekday},
        };

        #[test]
        fn test_process_specific_day_valid() {
            let datetime = Local::now();

            let monday_rule = Rule::monday;
            let tuesday_rule = Rule::tuesday;
            let wednesday_rule = Rule::wednesday;
            let thursday_rule = Rule::thursday;
            let friday_rule = Rule::friday;
            let saturday_rule = Rule::saturday;
            let sunday_rule = Rule::sunday;

            assert_specific_day_result(
                crate::process_specific_day(monday_rule, datetime),
                Weekday::Mon,
            );
            assert_specific_day_result(
                crate::process_specific_day(tuesday_rule, datetime),
                Weekday::Tue,
            );
            assert_specific_day_result(
                crate::process_specific_day(wednesday_rule, datetime),
                Weekday::Wed,
            );
            assert_specific_day_result(
                crate::process_specific_day(thursday_rule, datetime),
                Weekday::Thu,
            );
            assert_specific_day_result(
                crate::process_specific_day(friday_rule, datetime),
                Weekday::Fri,
            );
            assert_specific_day_result(
                crate::process_specific_day(saturday_rule, datetime),
                Weekday::Sat,
            );
            assert_specific_day_result(
                crate::process_specific_day(sunday_rule, datetime),
                Weekday::Sun,
            );
        }

        #[test]
        fn test_process_specific_day_invalid() {
            let invalid_rule = Rule::EOI;
            let datetime = Local::now();

            let result = crate::process_specific_day(invalid_rule, datetime);

            assert!(result.is_err());
            if let Err(ParseDateError::ParseError(msg)) = result {
                assert_ne!(msg, "");
            } else {
                panic!("Expected an error for invalid weekday");
            }
        }

        #[test]
        fn test_process_specific_day_with_future_weekday() {
            let datetime = Local::now();
            let next_monday_rule = Rule::monday;
            let result = crate::process_specific_day(next_monday_rule, datetime);

            assert_specific_day_result(result, Weekday::Mon);
        }
    }

    #[cfg(test)]
    mod process_specific_time_tests {
        use {
            crate::{
                ParseDateError,
                parser::{DateParser, Rule},
            },
            chrono::{DateTime, Local, TimeZone, Timelike},
            pest::{Parser, iterators::Pair},
        };

        fn get_test_datetime() -> DateTime<Local> {
            Local.with_ymd_and_hms(2024, 11, 11, 12, 0, 0).unwrap()
        }

        #[expect(clippy::result_large_err)]
        fn parse_input(input: &str) -> Result<Pair<'_, Rule>, pest::error::Error<Rule>> {
            let pair = DateParser::parse(Rule::specific_time, input)?;
            Ok(pair.into_iter().next().unwrap())
        }

        #[test]
        fn test_process_specific_time_am() {
            let datetime = get_test_datetime();
            let input = "9:45AM";

            let pair = parse_input(input).unwrap();

            let result = crate::process_specific_time(pair, datetime);

            assert!(result.is_ok());
            let modified_datetime = result.unwrap();
            assert_eq!(modified_datetime.hour(), 9);
            assert_eq!(modified_datetime.minute(), 45);
        }

        #[test]
        fn test_process_specific_time_pm() {
            let datetime = get_test_datetime();
            let pair = parse_input("5:30PM").unwrap();

            let result = crate::process_specific_time(pair, datetime);

            assert!(result.is_ok());
            let modified_datetime = result.unwrap();
            assert_eq!(modified_datetime.hour(), 17);
            assert_eq!(modified_datetime.minute(), 30);
        }

        #[test]
        fn test_process_specific_time_midnight() {
            let datetime = get_test_datetime();
            let pair = parse_input("12:00AM").unwrap();
            let result = crate::process_specific_time(pair, datetime);

            assert!(result.is_ok());
            let modified_datetime = result.unwrap();
            assert_eq!(modified_datetime.hour(), 0);
            assert_eq!(modified_datetime.minute(), 0);
        }

        #[test]
        fn test_process_specific_time_noon() {
            let datetime = get_test_datetime();
            let pair = parse_input("12:00PM").unwrap();
            let result = crate::process_specific_time(pair, datetime);

            assert!(result.is_ok());
            let modified_datetime = result.unwrap();
            assert_eq!(modified_datetime.hour(), 12);
            assert_eq!(modified_datetime.minute(), 0);
        }

        #[test]
        fn test_process_specific_time_invalid() {
            let datetime = get_test_datetime();

            let pair = parse_input("25:00PM").unwrap();
            let result = crate::process_specific_time(pair, datetime);

            assert!(result.is_err());
            if let Err(ParseDateError::ParseError(msg)) = result {
                assert!(msg.contains("Invalid hour"));
            } else {
                panic!("Expected error for invalid time");
            }
        }

        #[test]
        fn test_process_specific_time_same_time() {
            let datetime = get_test_datetime();

            let pair = parse_input("10:30AM").unwrap(); // create Pair for "10:30AM" input;
            let result = crate::process_specific_time(pair, datetime);

            assert!(result.is_ok());
            let modified_datetime = result.unwrap();
            assert_eq!(modified_datetime.hour(), 10);
            assert_eq!(modified_datetime.minute(), 30);
        }
    }

    #[cfg(test)]
    mod process_specific_day_and_time_tests {
        use {
            crate::parser::{DateParser, Rule},
            chrono::{DateTime, Datelike, Local, TimeZone, Timelike, Weekday},
            pest::{Parser, iterators::Pair},
        };

        fn get_test_datetime() -> DateTime<Local> {
            Local.with_ymd_and_hms(2025, 9, 7, 12, 0, 0).unwrap()
        }

        #[expect(clippy::result_large_err)]
        fn parse_input(input: &str) -> Result<Pair<'_, Rule>, pest::error::Error<Rule>> {
            let pair = DateParser::parse(Rule::specific_day_and_time, input)?;
            Ok(pair.into_iter().next().unwrap())
        }

        #[test]
        fn test_process_specific_day_and_time_am() {
            let datetime = get_test_datetime();
            let input = "monday at 9:45AM";

            let pair = parse_input(input).unwrap();

            let result = crate::process_specific_day_and_time(pair, datetime);

            assert!(result.is_ok());
            let modified_datetime = result.unwrap();
            assert_eq!(modified_datetime.hour(), 9);
            assert_eq!(modified_datetime.minute(), 45);
            assert_eq!(modified_datetime.day(), 8);
            assert_eq!(modified_datetime.weekday(), Weekday::Mon);
        }
    }

    #[cfg(test)]
    mod process_specific_date_and_time_tests {
        use {
            crate::parser::{DateParser, Rule},
            chrono::{DateTime, Datelike, Local, TimeZone, Timelike},
            pest::{Parser, iterators::Pair},
        };

        fn get_test_datetime() -> DateTime<Local> {
            Local.with_ymd_and_hms(2025, 9, 7, 12, 0, 0).unwrap()
        }

        #[expect(clippy::result_large_err)]
        fn parse_input(input: &str) -> Result<Pair<'_, Rule>, pest::error::Error<Rule>> {
            let pair = DateParser::parse(Rule::specific_date_and_time, input)?;
            Ok(pair.into_iter().next().unwrap())
        }

        #[test]
        fn test_process_specific_date_and_time_am() {
            let datetime = get_test_datetime();
            let input = "2025.11.11 at 9:45AM";

            let pair = parse_input(input).unwrap();

            let result = crate::process_specific_date_and_time(pair, datetime);

            assert!(result.is_ok());
            let modified_datetime = result.unwrap();
            assert_eq!(modified_datetime.hour(), 9);
            assert_eq!(modified_datetime.minute(), 45);
            assert_eq!(modified_datetime.year(), 2025);
            assert_eq!(modified_datetime.month(), 11);
            assert_eq!(modified_datetime.day(), 11);
        }
    }

    #[cfg(test)]
    mod process_relative_term_tests {
        use {
            crate::parser::{DateParser, Rule},
            chrono::{DateTime, Datelike, Duration, Local},
            pest::Parser,
        };

        fn test_relative_term_rule(input: &str, expected_datetime: DateTime<Local>) {
            let pair = DateParser::parse(Rule::relative_term, input)
                .unwrap()
                .next()
                .unwrap();

            let result = crate::process_relative_term(pair, Local::now());
            assert!(result.is_ok());
            assert_eq!(result.as_ref().unwrap().year(), expected_datetime.year());
            assert_eq!(result.as_ref().unwrap().month(), expected_datetime.month());
            assert_eq!(result.unwrap().day(), expected_datetime.day());
        }

        #[test]
        fn test_process_relative_term_tomorrow() {
            let tomorrow = Local::now() + Duration::days(1);
            test_relative_term_rule("tomorrow", tomorrow);
        }

        #[test]
        fn test_process_relative_term_today() {
            let today = Local::now();
            test_relative_term_rule("today", today);
        }

        #[test]
        fn test_process_relative_term_yesterday() {
            let yesterday = Local::now() - Duration::days(1);
            test_relative_term_rule("yesterday", yesterday);
        }
    }

    #[cfg(test)]
    mod process_relative_date_tests {
        use {
            crate::parser::{DateParser, Rule},
            chrono::{Datelike, Duration, Local},
            pest::Parser,
        };

        #[test]
        fn test_process_relative_date_next_monday() {
            let today_weekday = Local::now().weekday();
            let target_weekday = chrono::Weekday::Mon;
            let days_offset =
                if today_weekday.num_days_from_monday() <= target_weekday.num_days_from_monday() {
                    (target_weekday.num_days_from_monday() as i64)
                        - (today_weekday.num_days_from_monday() as i64)
                } else {
                    7 - ((today_weekday.num_days_from_monday() as i64)
                        - (target_weekday.num_days_from_monday() as i64))
                };

            let pair = DateParser::parse(Rule::relative_date, "next Monday")
                .unwrap()
                .next()
                .unwrap();

            let result = crate::process_relative_date(pair, Local::now());
            assert!(result.is_ok());

            let expected_date = Local::now() + Duration::days(days_offset);
            assert_eq!(result.unwrap().date_naive(), expected_date.date_naive());
        }
    }

    #[test]
    fn test_in_15_minutes() {
        assert_eq!(
            crate::from_string_with_reference(
                "in 15 minutes",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2025, 9, 7, 21, 15, 0).unwrap()
        )
    }

    #[test]
    fn test_in_1_hour() {
        assert_eq!(
            crate::from_string_with_reference(
                "in 1 hour",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2025, 9, 7, 22, 0, 0).unwrap()
        )
    }

    #[test]
    fn test_in_3_days() {
        assert_eq!(
            crate::from_string_with_reference(
                "in 3 days",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2025, 9, 10, 21, 0, 0).unwrap()
        )
    }

    #[test]
    fn test_in_5_weeks() {
        assert_eq!(
            crate::from_string_with_reference(
                "in 5 weeks",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2025, 10, 12, 21, 0, 0).unwrap()
        )
    }

    #[test]
    fn test_in_2_months() {
        assert_eq!(
            crate::from_string_with_reference(
                "in 2 months",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2025, 11, 7, 21, 0, 0).unwrap()
        )
    }

    #[test]
    fn test_in_12_years() {
        assert_eq!(
            crate::from_string_with_reference(
                "in 12 years",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2037, 9, 7, 21, 0, 0).unwrap()
        )
    }

    // #[test]
    // fn test_specific_date() {
    //     assert_eq!(
    //         crate::from_string("2025/Sep/27",).unwrap(),
    //         Local.with_ymd_and_hms(2025, 9, 27, 13, 33, 0).unwrap()
    //     );
    // }

    #[test]
    fn test_specific_day_and_time() {
        assert_eq!(
            crate::from_string_with_reference(
                "monday at 1:33 PM",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2025, 9, 8, 13, 33, 0).unwrap()
        );
        assert_eq!(
            crate::from_string_with_reference(
                "tuesday at 1 Pm",
                Local.with_ymd_and_hms(2025, 9, 7, 21, 0, 0).unwrap()
            )
            .unwrap(),
            Local.with_ymd_and_hms(2025, 9, 9, 13, 0, 0).unwrap()
        );
    }

    #[test]
    fn test_specific_date_and_time() {
        assert_eq!(
            crate::from_string("2025/Sep/27 at 1:33 PM").unwrap(),
            Local.with_ymd_and_hms(2025, 9, 27, 13, 33, 0).unwrap()
        );
        assert_eq!(
            crate::from_string("2025/Sep/7 at 1 Pm").unwrap(),
            Local.with_ymd_and_hms(2025, 9, 7, 13, 0, 0).unwrap()
        );
    }

    /// Time adjustment utilities tests

    #[test]
    fn test_change_time_valid() {
        let now = Local::now();

        let new_time = crate::change_time(now, 16, 45);
        assert!(new_time.is_ok());

        let new_datetime = new_time.unwrap();
        assert_eq!(new_datetime.hour(), 16);
        assert_eq!(new_datetime.minute(), 45);
    }

    #[test]
    fn test_change_time_invalid_hour() {
        let now = Local::now();

        let new_time = crate::change_time(now, 25, 30);
        assert!(new_time.is_err());

        if let Err(ParseDateError::ParseError(msg)) = new_time {
            assert_eq!(msg, "Invalid date or time components");
        } else {
            panic!("Expected an error with invalid time");
        }
    }

    #[test]
    fn test_change_time_invalid_minute() {
        let now = Local::now();

        let new_time = crate::change_time(now, 14, 60);
        assert!(new_time.is_err());

        if let Err(ParseDateError::ParseError(msg)) = new_time {
            assert_eq!(msg, "Invalid date or time components");
        } else {
            panic!("Expected an error with invalid time");
        }
    }

    #[test]
    fn test_adjust_to_next_weekday() {
        // Monday
        let datetime = Local.with_ymd_and_hms(2024, 11, 11, 12, 0, 0).unwrap();

        let adjusted_date = crate::shift_to_weekday(datetime, Weekday::Fri, Rule::next);
        assert!(adjusted_date.is_ok());
        assert_eq!(adjusted_date.as_ref().unwrap().weekday(), Weekday::Fri);
        assert_eq!(adjusted_date.unwrap().year(), datetime.year());

        let adjusted_date = crate::shift_to_weekday(datetime, Weekday::Mon, Rule::next);
        assert!(adjusted_date.is_ok());
        assert_eq!(adjusted_date.as_ref().unwrap().weekday(), Weekday::Mon);
        assert_eq!(adjusted_date.unwrap().year(), datetime.year());
    }

    #[test]
    fn test_adjust_to_last_weekday() {
        let now = Local::now();
        let weekday = now.weekday();

        let adjusted_date = crate::shift_to_weekday(now, weekday, Rule::last);
        assert!(adjusted_date.is_ok());
        assert_eq!(adjusted_date.as_ref().unwrap().weekday(), weekday);
        assert_eq!(now - adjusted_date.unwrap(), Duration::days(7));
    }

    #[test]
    fn test_adjust_to_this_weekday() {
        let now = Local::now();
        let weekday = now.weekday();

        let adjusted_date = crate::shift_to_weekday(now, weekday, Rule::this);
        assert!(adjusted_date.is_ok());
        assert_eq!(adjusted_date.unwrap(), now);
    }
}
