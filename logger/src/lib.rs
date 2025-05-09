//! Logging utilities.

use eyre::{Context as _, Result};
use tracing::{Level, level_filters::LevelFilter};
use tracing_subscriber::{EnvFilter, FmtSubscriber};

pub use tracing::{
    Instrument, Span, debug, debug_span, error, error_span, info, info_span, trace, trace_span,
    warn, warn_span,
};

/// Initialize logger.
pub fn init_logger() -> Result<()> {
    let subscriber = FmtSubscriber::builder()
        .with_max_level(Level::TRACE)
        .with_env_filter(
            EnvFilter::builder()
                .with_default_directive(LevelFilter::INFO.into())
                .from_env_lossy(),
        )
        .finish();
    tracing::subscriber::set_global_default(subscriber).wrap_err("failed to set global logger")
}
