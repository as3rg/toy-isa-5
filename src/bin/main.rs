use std::fs::File;
use std::io::BufReader;
use std::process;

use clap::{Arg, Command, builder::TypedValueParser};
use jit::{
    cpu::CPUState,
    globals::{ExecError, Pc, Utarget},
    runner::{execute, interpret},
};

fn main() {
    env_logger::init();

    let matches = Command::new("toy5")
        .version("0.1")
        .arg(
            Arg::new("file")
                .value_name("FILE")
                .help("The file to interpert")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::new("jit")
                .short('j')
                .long("jit")
                .help("Use jit")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("start")
                .short('s')
                .long("start")
                .help("Entry point in a file")
                .default_value("0")
                .value_parser(clap::value_parser!(Utarget).map(Pc)),
        )
        .get_matches();

    let filename = matches.get_one::<String>("file").unwrap();
    let jit = matches.get_flag("jit");
    let entry = *matches.get_one::<Pc>("start").unwrap();

    let mut cpu = CPUState::default();

    let res = match File::open(filename) {
        Ok(file) => {
            let mut reader = BufReader::new(file);
            if jit {
                execute(&mut cpu, &mut reader, entry)
            } else {
                interpret(&mut cpu, &mut reader, entry)
            }
        }
        Err(e) => {
            println!("Error occured while opening the file: {}", e);
            process::exit(1);
        }
    };

    match res {
        Ok(_) => process::exit(0),
        Err(ExecError::Exit { exit_code }) => process::exit(exit_code.cast_signed()),
        Err(e) => {
            println!("Error occured while executing: {}", e);
            process::exit(1);
        }
    }
}
