# Natural Date Parser

- Crates: https://lib.rs/crates/natural-date-rs
- Docs: https://docs.rs/natural-date-rs

## Brief Description

A parser to convert natural language date and time specification into a DateTime.

Parse expressions, such as "next Monday," "tomorrow at 5 PM," or "3 weeks from now." This parser converts these expressions into structured `DateTime` objects, making them usable in scheduling applications, reminders, or other time-based software.

## Technical Description

The parser is built using the [Pest](https://pest.rs/) parser library. It recognizes a variety of phrases related to dates and times, for example:

- **Simple Relative Dates**: "today," "tomorrow," "yesterday."
- **Day of the Week Expressions**: "next Monday," "last Friday."
- **Complex Relative Time Expressions**: "in 3 days," "2 weeks from now," "4 months ago."
- **Combined Date and Time Expressions**: "next Thursday at 10 AM," "tomorrow at 5:30 PM."
