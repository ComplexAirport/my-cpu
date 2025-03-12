fn main() {
    let p = lalrpop::process_root();
    if p.is_err() {
        eprintln!("{}", p.unwrap_err());
        panic!();
    }
}