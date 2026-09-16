extern crate core;

use crate::error::ErrorReported;

mod ast;
mod codegen;
pub mod error;
pub mod parser;
#[allow(clippy::result_large_err)]
pub mod ty_check;

pub fn compile(file_path: &str) -> Result<String, ErrorReported> {
    compile_with_observer(file_path, &mut NoopObserver)
}

#[derive(Clone, Copy)]
enum CompilePhase {
    SourceLoad,
    AstPreparation,
    TypeCheck,
    Codegen,
    Teardown,
}

trait CompileObserver {
    fn start(&mut self, _phase: CompilePhase) {}
    fn finish(&mut self, _phase: CompilePhase) {}
}

struct NoopObserver;

impl CompileObserver for NoopObserver {}

fn compile_with_observer(
    file_path: &str,
    observer: &mut impl CompileObserver,
) -> Result<String, ErrorReported> {
    observer.start(CompilePhase::SourceLoad);
    let source = parser::SourceCode::from_file(file_path)?;
    observer.finish(CompilePhase::SourceLoad);

    observer.start(CompilePhase::AstPreparation);
    let mut compil_unit = parser::parse(&source)?;
    observer.finish(CompilePhase::AstPreparation);

    observer.start(CompilePhase::TypeCheck);
    ty_check::ty_check(&mut compil_unit)?;
    observer.finish(CompilePhase::TypeCheck);

    observer.start(CompilePhase::Codegen);
    let cuda = codegen::gen(&compil_unit);
    observer.finish(CompilePhase::Codegen);

    observer.start(CompilePhase::Teardown);
    drop(compil_unit);
    drop(source);
    observer.finish(CompilePhase::Teardown);

    Ok(cuda)
}

#[derive(Debug)]
pub struct CompileMetrics {
    pub source_load: std::time::Duration,
    pub ast_preparation: std::time::Duration,
    pub type_check: std::time::Duration,
    pub codegen: std::time::Duration,
    pub teardown: std::time::Duration,
    pub total: std::time::Duration,
    pub arena_allocated_bytes: Option<usize>,
    pub cuda: String,
}

struct TimingObserver {
    total_start: std::time::Instant,
    phase_start: std::time::Instant,
    source_load: std::time::Duration,
    ast_preparation: std::time::Duration,
    type_check: std::time::Duration,
    codegen: std::time::Duration,
    teardown: std::time::Duration,
}

impl TimingObserver {
    fn new() -> Self {
        let now = std::time::Instant::now();
        Self {
            total_start: now,
            phase_start: now,
            source_load: std::time::Duration::ZERO,
            ast_preparation: std::time::Duration::ZERO,
            type_check: std::time::Duration::ZERO,
            codegen: std::time::Duration::ZERO,
            teardown: std::time::Duration::ZERO,
        }
    }

    fn into_metrics(self, cuda: String) -> CompileMetrics {
        CompileMetrics {
            source_load: self.source_load,
            ast_preparation: self.ast_preparation,
            type_check: self.type_check,
            codegen: self.codegen,
            teardown: self.teardown,
            total: self.total_start.elapsed(),
            arena_allocated_bytes: None,
            cuda,
        }
    }
}

impl CompileObserver for TimingObserver {
    fn start(&mut self, _phase: CompilePhase) {
        self.phase_start = std::time::Instant::now();
    }

    fn finish(&mut self, phase: CompilePhase) {
        let elapsed = self.phase_start.elapsed();
        match phase {
            CompilePhase::SourceLoad => self.source_load = elapsed,
            CompilePhase::AstPreparation => self.ast_preparation = elapsed,
            CompilePhase::TypeCheck => self.type_check = elapsed,
            CompilePhase::Codegen => self.codegen = elapsed,
            CompilePhase::Teardown => self.teardown = elapsed,
        }
    }
}

pub fn compile_measured(file_path: &str) -> Result<CompileMetrics, ErrorReported> {
    let mut observer = TimingObserver::new();
    let cuda = compile_with_observer(file_path, &mut observer)?;
    Ok(observer.into_metrics(cuda))
}
