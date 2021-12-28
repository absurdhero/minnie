use crate::CompilerError;
use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFile;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

///! Configures and wraps the codespan_reporting library.

/// Convenience function for printing an error in a single source file in one step.
///
/// We don't care about re-initializing everything each time we print because it happens so rarely.
/// Especially since there is currently no error recovery that could cause many errors in a row.
pub fn print_error(
    source_name: &str,
    source: &str,
    error: CompilerError<'_>,
) -> Result<(), anyhow::Error> {
    let reporter = ErrorReporting::new();
    reporter.print(source_name, source, &error)
}

pub struct ErrorReporting {
    writer: StandardStream,
    term_config: codespan_reporting::term::Config,
}

impl ErrorReporting {
    pub fn new() -> ErrorReporting {
        ErrorReporting {
            writer: StandardStream::stderr(ColorChoice::Always),
            term_config: codespan_reporting::term::Config::default(),
        }
    }

    pub fn print(
        &self,
        source_name: &str,
        source: &str,
        error: &CompilerError,
    ) -> Result<(), anyhow::Error> {
        let mut diagnostic = Diagnostic::error();
        if let Some(ref s) = error.span {
            diagnostic = diagnostic.with_labels(vec![
                Label::primary((), s.clone()).with_message(error.to_string())
            ]);
        } else {
            diagnostic = diagnostic.with_message(error.to_string());
        };

        // we only support one source file right now.
        let file = SimpleFile::new(source_name, source);

        codespan_reporting::term::emit(
            &mut self.writer.lock(),
            &self.term_config,
            &file,
            &diagnostic,
        )
        .map_err(anyhow::Error::from)
    }
}
