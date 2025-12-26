use {natural_date_rs as date_parser, std::env};

/// CLI interface
fn main() -> anyhow::Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        println!("Date Parser CLI - Usage:");
        println!(
            "  cargo run <date_string>     Parses a date written in English and displays its components."
        );
        return Ok(());
    }

    match date_parser::from_string(args[1].as_str()) {
        Ok(parsed) => println!("{:#?}", parsed),
        Err(e) => eprintln!("Error: {}", e),
    }

    Ok(())
}
