mod cu_ast;
mod printer;

use crate::ast as desc;
use cu_ast as cu;

// Precondition. all function defitions are successfully typechecked and
// therefore every subexpression stores a type
pub fn gen(program: &desc::GlobalCtx) -> String {
    let cu_program = gen_cuda(program);
    printer::print(&cu_program)
}

fn gen_cuda(program: &desc::GlobalCtx) -> cu::CuProgram {
    let fun_defs = program.fun_defs();
    fun_defs.map(gen_fun_def).collect::<cu::CuProgram>()
}

fn gen_fun_def(gl_fun: &desc::GlobalFunDef) -> cu::Item {
    let desc::GlobalFunDef {
        name,
        ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels,
        body_expr,
        fun_ty,
    } = gl_fun;

    let fun_def = cu::Item::FunDef {
        name: name.clone(),
        templ_params: gen_templ_params(ty_idents),
        params: gen_param_decls(params),
        ret_ty: gen_ty(ret_ty),
        body: gen_stmts(body_expr),
        is_dev_fun: is_dev_fun(*exec),
    };

    unimplemented!()
}

fn gen_templ_params(ty_idents: &[desc::IdentKinded]) -> Vec<cu::TemplParam> {
    unimplemented!()
}

fn gen_param_decls(params: &[desc::IdentTyped]) -> Vec<cu::ParamDecl> {
    unimplemented!()
}

fn gen_ty(ty: &desc::Ty) -> cu::Ty {
    unimplemented!()
}

fn gen_stmts(expr: &desc::Expr) -> Vec<cu::Stmt> {
    unimplemented!()
}

fn is_dev_fun(exec: desc::ExecLoc) -> bool {
    match exec {
        // TODO correct?
        desc::ExecLoc::GpuGroup | desc::ExecLoc::GpuThread => true,
        desc::ExecLoc::CpuThread => false,
    }
}
