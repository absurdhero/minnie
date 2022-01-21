use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFile;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream, WriteColor};
use std::ops::Range;

use crate::compiler::{CompilerError, ErrorType};

///! Configures and wraps the `codespan_reporting` library.

/// Convenience function for printing errors in a single source file in one step.
pub fn print_error(
    source_name: &str,
    source: &str,
    errors: &[CompilerError],
) -> Result<(), anyhow::Error> {
    let reporter = ErrorReporting::default();
    let writer = StandardStream::stderr(ColorChoice::Always);
    for error in errors {
        reporter.print(&mut writer.lock(), source_name, source, error)?;
    }
    Ok(())
}

pub struct ErrorReporting {
    term_config: codespan_reporting::term::Config,
}
impl Default for ErrorReporting {
    fn default() -> Self {
        ErrorReporting::new(codespan_reporting::term::Config::default())
    }
}

impl ErrorReporting {
    pub fn new(term_config: codespan_reporting::term::Config) -> ErrorReporting {
        ErrorReporting { term_config }
    }

    pub fn print(
        &self,
        writer: &mut dyn WriteColor,
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
                            Label::secondary((), Range::from(secondary))
                                .with_message(secondary.to_string()),
                        );
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

        codespan_reporting::term::emit(writer, &self.term_config, &file, &diagnostic)
            .map_err(anyhow::Error::from)
    }
}

pub mod test_util {
    use crate::compiler::CompilerError;
    use crate::error_reporting::ErrorReporting;
    use codespan_reporting::term::termcolor;
    use std::cell::RefCell;
    use std::io;

    /// render a list of compiler errors to a String for verification by tests
    pub fn capture_errors(
        source_name: &str,
        source: &str,
        errors: &[CompilerError],
    ) -> Result<String, anyhow::Error> {
        let reporter = ErrorReporting::default();
        let mut writer = termcolor::NoColor::new(CaptureInput::new());
        for error in errors {
            reporter.print(&mut writer, source_name, source, error)?;
        }
        Ok(writer.into_inner().0.into_inner())
    }

    /// A writer that captures data written to it as a String.
    struct CaptureInput(RefCell<String>);

    impl CaptureInput {
        fn new() -> CaptureInput {
            CaptureInput(RefCell::new(String::new()))
        }
    }

    impl io::Write for CaptureInput {
        #[inline]
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            // we are consuming our program's own output so we know it is UTF-8 safe
            unsafe { self.0.borrow_mut().as_mut_vec().write(buf) }
        }

        #[inline]
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }
}
