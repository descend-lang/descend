use crate::ast::{
    BaseTy, BinOpNat, DataTy, DataTyKind, Dim, DimCompo, ExecTy, ExecTyKind, Ident, IdentKinded,
    IdentTyped, Kind, Memory, Nat, Ownership, Predicate, Provenance, Refinement, ScalarTy, Ty,
    TyKind,
};

pub struct PrintState {
    string: String,
}

macro_rules! print_list {
    ($print_state: ident, $print_fun: path, $list: expr) => {
        for elem in $list {
            $print_fun($print_state, elem);
            $print_state.string.push(',');
        }
    };
}

macro_rules! print_static_list {
    ($print_state: ident, $print_fun: path, $($item: expr),*) => {
        $(
            $print_fun($print_state, $item);
            $print_state.string.push(',');
        )*
    };
}

impl PrintState {
    pub fn new() -> Self {
        PrintState {
            string: String::new(),
        }
    }

    pub fn get(&self) -> String {
        self.string.clone()
    }

    fn print_ident(&mut self, ident: &Ident) {
        self.string.push_str(&ident.name);
    }

    fn print_ty(&mut self, ty: &Ty) {
        match &ty.ty {
            TyKind::FnTy(fn_ty) => {
                self.string.push('<');
                print_list!(self, Self::print_ident_kinded, &fn_ty.generics);
                self.string.push_str(">(");
                print_list!(self, Self::print_ident_typed, &fn_ty.idents_typed);
                self.string.push_str(") -[");
                self.print_exec_ty(&fn_ty.exec_ty);
            }
            TyKind::Data(dty) => self.print_dty(dty),
        }
    }

    fn print_ident_typed(&mut self, ident_typed: &IdentTyped) {
        self.print_ident(&ident_typed.ident);
        self.string.push_str(" : ");
        self.print_dty(&ident_typed.dty);
    }

    fn print_ident_kinded(&mut self, ident_kinded: &IdentKinded) {
        self.print_ident(&ident_kinded.ident);
        self.string.push_str(" : ");
        self.print_kind(ident_kinded.kind);
    }

    fn print_kind(&mut self, kind: Kind) {
        let kind_str = match kind {
            Kind::DataTy => "dty",
            Kind::Provenance => "prv",
            Kind::Memory => "mem",
            Kind::Nat => "nat",
        };
        self.string.push_str(kind_str);
    }

    fn print_exec_ty(&mut self, exec_ty: &ExecTy) {
        match &exec_ty.ty {
            ExecTyKind::CpuThread => self.string.push_str("cpu.thread"),
            ExecTyKind::GpuGrid(gdim, bdim) => {
                self.string.push_str("gpu.grid<");
                print_static_list!(self, Self::print_dim, gdim, bdim);
                self.string.push('>');
            }
            ExecTyKind::GpuGlobalThreads(dim) => {
                self.string.push_str("gpu.global_threads<");
                self.print_dim(dim);
                self.string.push('>');
            }
            ExecTyKind::GpuBlock(bdim) => {
                self.string.push_str("gpu.block<");
                self.print_dim(bdim);
                self.string.push('>');
            }
            ExecTyKind::GpuThread => self.string.push_str("gpu.thread"),
            ExecTyKind::GpuBlockGrp(gdim, bdim) => {
                self.string.push_str("gpu.block_grp<");
                print_static_list!(self, Self::print_dim, gdim, bdim);
                self.string.push('>');
            }
            ExecTyKind::GpuThreadGrp(dim) => {
                self.string.push_str("gpu.thread_grp<");
                self.print_dim(dim);
                self.string.push('>');
            }
            ExecTyKind::View => self.string.push_str("view"),
        }
    }

    fn print_dim(&mut self, dim: &Dim) {
        match dim {
            Dim::XYZ(dim3d) => {
                self.string.push_str("XYZ<");
                print_static_list!(self, Self::print_pred, &dim3d.0, &dim3d.1, &dim3d.2);
            }
            Dim::XY(dim2d) => {
                self.string.push_str("XY<");
                print_static_list!(self, Self::print_pred, &dim2d.0, &dim2d.1);
            }
            Dim::XZ(dim2d) => {
                self.string.push_str("XZ<");
                print_static_list!(self, Self::print_pred, &dim2d.0, &dim2d.1);
            }
            Dim::YZ(dim2d) => {
                self.string.push_str("YZ<");
                print_static_list!(self, Self::print_pred, &dim2d.0, &dim2d.1);
            }
            Dim::X(dim1d) => {
                self.string.push_str("X<");
                self.print_pred(&dim1d.0)
            }
            Dim::Y(dim1d) => {
                self.string.push_str("Y<");
                self.print_pred(&dim1d.0)
            }
            Dim::Z(dim1d) => {
                self.string.push_str("Z<");
                self.print_pred(&dim1d.0)
            }
        }
        self.string.push('>');
    }

    fn print_dim_compo(&mut self, dim_compo: &DimCompo) {
        match dim_compo {
            DimCompo::X => self.string.push('X'),
            DimCompo::Y => self.string.push('Y'),
            DimCompo::Z => self.string.push('Z'),
        }
    }

    pub fn print_dty(&mut self, dty: &DataTy) {
        match &dty.dty {
            DataTyKind::Ident(ident) => self.print_ident(ident),
            DataTyKind::Scalar(sty) => self.print_sty(sty),
            DataTyKind::Atomic(sty) => {
                self.string.push_str("Atomic<");
                self.print_sty(sty);
                self.string.push('>');
            }
            DataTyKind::Array(dty, n) => {
                self.string.push('[');
                self.print_dty(dty);
                self.string.push(';');
                self.print_pred(n);
                self.string.push(']');
            }
            DataTyKind::ArrayShape(dty, n) => {
                self.string.push_str("[[");
                self.print_dty(dty);
                self.string.push(';');
                self.print_pred(n);
                self.string.push_str("]]");
            }
            DataTyKind::Tuple(dtys) => {
                self.string.push('(');
                print_list!(self, Self::print_dty, dtys);
                self.string.push(')');
            }
            DataTyKind::At(dty, mem) => {
                self.print_dty(dty);
                self.string.push('@');
                self.print_mem(mem);
            }
            DataTyKind::Ref(ref_dty) => {
                self.string.push('&');
                self.print_prv(&ref_dty.rgn);
                self.string.push(' ');
                self.print_own(ref_dty.own);
                self.string.push(' ');
                self.print_mem(&ref_dty.mem);
                self.string.push(' ');
                self.print_dty(&ref_dty.dty);
            }
            DataTyKind::Refine(base_ty, refinement) => {
                self.string.push_str(match base_ty {
                    BaseTy::Bool => "bool",
                    BaseTy::Usize => "usize",
                });
                self.print_refine(refinement)
            }
            DataTyKind::RawPtr(_) => {
                unimplemented!()
            }
            DataTyKind::Range => self.string.push_str("Range"),
            DataTyKind::Dead(dty) => self.print_dty(dty),
        }
    }

    fn print_refine(&mut self, refine: &Refinement) {
        self.string.push('[');
        self.print_ident(&refine.ident);
        self.string.push_str(" | ");
        self.print_pred(&refine.pred);
        self.string.push(']');
    }

    fn print_pred(&mut self, pred: &Predicate) {
        match pred {
            Predicate::Ident(ident) => self.print_ident(ident),
            Predicate::Add(predl, predr) => {
                self.print_pred(predl);
                self.string.push_str(" + ");
                self.print_pred(predr);
            }
            Predicate::And(predl, predr) => {
                self.print_pred(predl);
                self.string.push_str(" & ");
                self.print_pred(predr);
            }
            Predicate::Or(predl, predr) => {
                self.print_pred(predl);
                self.string.push_str(" | ");
                self.print_pred(predr);
            }
            Predicate::ConstMul(c, pred) => {
                self.string.push_str(&c.to_string());
                self.string.push_str(" * ");
                self.print_pred(pred);
            }
            Predicate::IfElse(cond, tt, ff) => {
                self.string.push_str("if ");
                self.print_pred(cond);
                self.string.push_str(" then ");
                self.print_pred(tt);
                self.string.push_str(" else ");
                self.print_pred(ff);
            }
            Predicate::Not(pred) => {
                self.string.push_str("!(");
                self.print_pred(pred);
                self.string.push(')');
            }
            Predicate::Uninterp(ident, preds) => {
                self.print_ident(ident);
                print_list!(self, Self::print_pred, preds);
            }
            Predicate::False => self.string.push_str("false"),
            Predicate::True => self.string.push_str("true"),
            Predicate::Num(n) => {
                self.string.push_str(&n.to_string());
            }
            Predicate::Le(pl, pr) => {
                self.print_pred(pl);
                self.string.push_str(" < ");
                self.print_pred(pr);
            }
            Predicate::Eq(pl, pr) => {
                self.print_pred(pl);
                self.string.push_str(" = ");
                self.print_pred(pr);
            }
        }
    }

    fn print_sty(&mut self, sty: &ScalarTy) {
        match sty {
            ScalarTy::Unit => self.string.push_str("()"),
            ScalarTy::U32 => self.string.push_str("u32"),
            ScalarTy::U64 => self.string.push_str("u64"),
            ScalarTy::I32 => self.string.push_str("i32"),
            ScalarTy::I64 => self.string.push_str("i64"),
            ScalarTy::F32 => self.string.push_str("f32"),
            ScalarTy::F64 => self.string.push_str("f64"),
            ScalarTy::Bool => self.string.push_str("bool"),
            ScalarTy::Gpu => self.string.push_str("Gpu"),
        }
    }

    fn print_mem(&mut self, mem: &Memory) {
        match mem {
            Memory::CpuMem => self.string.push_str("cpu.mem"),
            Memory::GpuGlobal => self.string.push_str("gpu.global"),
            Memory::GpuShared => self.string.push_str("gpu.shared"),
            Memory::GpuLocal => self.string.push_str("gpu.local"),
            Memory::Ident(x) => self.print_ident(x),
        }
    }

    fn print_prv(&mut self, prv: &Provenance) {
        match prv {
            Provenance::Value(name) => self.string.push_str(&name),
            Provenance::Ident(ident) => self.print_ident(ident),
        }
    }

    fn print_own(&mut self, own: Ownership) {
        match own {
            Ownership::Shrd => self.string.push_str("shrd"),
            Ownership::Uniq => self.string.push_str("uniq"),
        }
    }

    fn print_nat(&mut self, n: &Nat) {
        match n {
            Nat::Ident(ident) => self.print_ident(ident),
            Nat::GridIdx => {} // print nothing
            Nat::BlockIdx(d) => {
                self.string.push_str("blockIdx.");
                self.print_dim_compo(d);
            }
            Nat::BlockDim(d) => {
                self.string.push_str("blockDim.");
                self.print_dim_compo(d);
            }
            Nat::ThreadIdx(d) => {
                self.string.push_str("threadIdx.");
                self.print_dim_compo(d);
            }
            Nat::Lit(n) => self.string.push_str(&n.to_string()),
            Nat::BinOp(op, lhs, rhs) => {
                self.string.push('(');
                self.print_nat(lhs);
                self.print_bin_op_nat(op);
                self.print_nat(rhs);
                self.string.push(')');
            }
            Nat::App(func, args) => {
                self.string.push_str("{}(");
                self.print_ident(func);
                if let Some((last, leading)) = args.split_last() {
                    for arg in leading {
                        self.print_nat(arg);
                    }
                    self.print_nat(last);
                    self.string.push(')');
                }
            }
        }
    }

    fn print_bin_op_nat(&mut self, bin_op_nat: &BinOpNat) {
        match bin_op_nat {
            BinOpNat::Add => self.string.push('+'),
            BinOpNat::Sub => self.string.push('-'),
            BinOpNat::Mul => self.string.push('*'),
            BinOpNat::Div => self.string.push('/'),
            BinOpNat::Mod => self.string.push('%'),
        }
    }
}
