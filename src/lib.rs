pub mod circuit;
pub mod ipa;
pub mod range;
mod vector_ops;

#[cfg(test)]
mod test {
    use std::sync::Once;

    static INIT: Once = Once::new();

    fn init_console_subscriber() {
        use tracing_subscriber::filter::EnvFilter;
        use tracing_subscriber::fmt::format::FmtSpan;
        use tracing_subscriber::fmt::time::UtcTime;
        let timer = UtcTime::rfc_3339();
        tracing_subscriber::fmt()
            .with_env_filter(EnvFilter::from_default_env())
            .with_span_events(FmtSpan::CLOSE)
            .with_timer(timer)
            .with_target(true)
            .with_thread_ids(false)
            .with_line_number(false)
            .with_file(false)
            .with_level(true)
            .with_ansi(true)
            .with_writer(std::io::stdout)
            .init();
    }

    #[ctor::ctor]
    fn setup_logger() {
        INIT.call_once(|| {
            init_console_subscriber();
        });
    }
}
