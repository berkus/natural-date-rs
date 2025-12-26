# Natural Date Parser

A parser to convert natural language date and time specification into a DateTime.

The parser recognizes a variety of phrases related to dates and times, such as "next Monday," "tomorrow at 5 PM," or "3 weeks from now." This parser converts these expressions into structured `DateTime` objects, making them usable in scheduling applications, reminders, or other time-based software.

- **Simple Relative Dates**: "today," "tomorrow," "yesterday."
- **Day of the Week Expressions**: "next Monday," "last Friday."
- **Complex Relative Time Expressions**: "in 3 days," "2 weeks from now," "4 months ago."
- **Combined Date and Time Expressions**: "next Thursday at 10 AM," "tomorrow at 5:30 PM."
