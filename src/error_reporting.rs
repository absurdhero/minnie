use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFile;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use crate::{CompilerError, ErrorType};

///! Configures and wraps the codespan_reporting library.

/// Convenience function for printing errors in a single source file in one step.
pub fn print_error(
    source_name: &str,
    source: &str,
    errors: &[CompilerError],
) -> Result<(), anyhow::Error> {
    let reporter = ErrorReporting::new();
    for error in errors {
        reporter.print(source_name, source, error)?;
    }
    Ok(())
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
        let mut labels = vec![];
        if let Some(ref s) = error.span {
            match &error.error {
                ErrorType::ParseError(_) => {
                    labels.push(Label::primary((), s.clone()).with_message(error.to_string()));
                }
                ErrorType::ErrNode(primary, remaining) => {
                    labels.push(Label::primary((), s.clone()).with_message(primary.to_string()));
                    for secondary in remaining {
                        labels.push(
                            Label::secondary((), s.clone()).with_message(secondary.to_string()),
                        )
                    }
                }
            }
        }

        let mut diagnostic = Diagnostic::error();
        diagnostic = diagnostic.with_labels(labels);

        if error.span.is_none() {
            diagnostic = diagnostic.with_message(error.to_string());
        }

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
