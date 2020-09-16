use super::ast::*;
use super::ty::*;

//TODO call this Program or something comparable?

// ∀ε ∈ Σ. Σ ⊢ ε
// --------------
//      ⊢ Σ
pub fn ty_check(mut gl_ctx: GlobalCtx) -> Result<GlobalCtx, String> {
    let (typed_gl_ctx, errs): (Vec<_>, Vec<_>) = gl_ctx
        .iter()
        .map(|gl_f| ty_check_global_fun_def(&gl_ctx, gl_f))
        .partition(Result::is_ok);

    if errs.is_empty() {
        Ok(typed_gl_ctx.into_iter().map(Result::unwrap).collect())
    } else {
        Err(errs.into_iter().map(Result::unwrap_err).collect())
    }
}

// Σ ⊢ fn f <List[φ], List[ρ], List[α]> (x1: τ1, ..., xn: τn) → τr where List[ρ1:ρ2] { e }
fn ty_check_global_fun_def(gl_ctx: &GlobalCtx, gf: &GlobalFunDef) -> Result<GlobalFunDef, String> {
    let GlobalFunDef {
        name,
        ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels,
        mut body_expr,
        fun_ty,
    } = gf.clone();
    let kind_ctx: KindCtx = KindCtx::new()
        .append_prv_rels(&prv_rels)
        .append_ty_idents(&ty_idents);
    prv_rels_use_declared_idents(&prv_rels, &kind_ctx)?;

    // TODO introduce proper Frame typing type
    // Build frame typing for this function
    let glf_frame = append_idents_typed(
        &vec![],
        params
            .clone()
            .into_iter()
            .map(|(ident, dty)| (ident, Ty::Data(dty)))
            .collect(),
    );
    let ty_ctx = vec![glf_frame];
    ty_check_expr(gl_ctx, &kind_ctx, &ty_ctx, &mut body_expr)?;

    // t <= t_f
    let empty_ty_ctx = subty_check(
        &kind_ctx,
        &ty_ctx,
        &body_expr.ty.as_ref().unwrap(),
        &Ty::Data(ret_ty.clone()),
    )?;
    assert!(empty_ty_ctx.is_empty(), "This should never happen.");

    Ok(GlobalFunDef {
        name,
        ty_idents,
        params,
        ret_ty,
        exec,
        prv_rels,
        body_expr,
        fun_ty,
    })
}

fn prv_rels_use_declared_idents(
    prv_rels: &Vec<(TyIdent, TyIdent)>,
    kind_ctx: &KindCtx,
) -> Result<(), String> {
    let prv_idents = kind_ctx.get_ty_idents_by_kind(Kind::Provenance);
    for prv_rel in prv_rels {
        if !prv_idents.contains(&prv_rel.0) {
            return Err(format!("{} is not declared", prv_rel.0));
        }
        if !prv_idents.contains(&prv_rel.1) {
            return Err(format!("{} is not declared", prv_rel.1));
        }
    }
    Ok(())
}

// TODO find out if Gamma is always correct by construction (similarly to Delta), also all 3 combined
// e has type τ under Σ, Δ, and Γ, producing output context Γ
// Σ; Δ; Γ ⊢ e : τ ⇒ Γ′
fn ty_check_expr(
    gl_ctx: &GlobalCtx,
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    expr: &mut Expr,
) -> Result<TypingCtx, String> {
    panic!("Not yet implemented.")
}

//
// Subtyping and Provenance Subtyping from Oxide
//

// τ1 is subtype of τ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ τ1 ≲ τ2 ⇒ Γ′
fn subty_check(
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    sub_ty: &Ty,
    super_ty: &Ty,
) -> Result<TypingCtx, String> {
    use DataTy::*;
    use Ownership::*;
    use Ty::*;

    match (sub_ty, super_ty) {
        // Δ; Γ ⊢ τ ≲ τ ⇒ Γ
        (sub, sup) if sub == sup => Ok(ty_ctx.clone()),
        // Δ; Γ ⊢ [τ 1 ; n] ≲ [τ2 ; n] ⇒ Γ′
        (Data(Array(sub_size, sub_elem_dty)), Data(Array(sup_size, sup_elem_dty)))
            if sub_size == sup_size =>
        {
            subty_check(
                kind_ctx,
                ty_ctx,
                &Data((**sub_elem_dty).clone()),
                &Data((**sup_elem_dty).clone()),
            )
        }
        // Δ; Γ ⊢ &ρ1 shrd τ1 ≲ &ρ2 shrd τ2 ⇒ Γ′′
        (
            Data(Ref(sub_prv, Shrd, sub_mem, sub_dty)),
            Data(Ref(sup_prv, Shrd, sup_mem, sup_dty)),
        ) if sub_mem == sup_mem => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            subty_check(
                kind_ctx,
                &res_outl_ty_ctx,
                &Data((**sub_dty).clone()),
                &Data((**sup_dty).clone()),
            )
        }
        // Δ; Γ ⊢ &ρ1 uniq τ1 ≲ &ρ2 uniq τ2 ⇒ Γ''
        (
            Data(Ref(sub_prv, Uniq, sub_mem, sub_dty)),
            Data(Ref(sup_prv, Uniq, sup_mem, sup_dty)),
        ) if sub_mem == sup_mem => {
            let res_outl_ty_ctx = outlives(kind_ctx, ty_ctx, sub_prv, sup_prv)?;
            let res_forw = subty_check(
                kind_ctx,
                &res_outl_ty_ctx,
                &Data((**sub_dty).clone()),
                &Data((**sup_dty).clone()),
            )?;
            let res_back = subty_check(
                kind_ctx,
                &res_outl_ty_ctx,
                &Data((**sup_dty).clone()),
                &Data((**sub_dty).clone()),
            )?;

            // TODO find out why this is important (techniqually),
            //  and return a proper error if suitable
            assert!(res_forw == res_back);
            Ok(res_back)
        }
        // Δ; Γ ⊢ (τ1, ..., τn) ≲ (τ1′, ..., τn′) ⇒ Γn
        // TODO Oxide uses a fix Gamma here that seems like a mistake.
        //  Therefore, think about this more. Currently, it starts with the input context and
        //  checks every subtyping relation sequentially from left to write, updating the ctx in the
        //  process.
        (Ty::Tuple(sub_elems), Ty::Tuple(sup_elems)) => {
            let mut res_ctx = ty_ctx.clone();
            for (sub, sup) in sub_elems.iter().zip(sup_elems) {
                res_ctx = subty_check(kind_ctx, &res_ctx, sub, sup)?;
            }
            Ok(res_ctx.clone())
        }
        // Δ; Γ ⊢ \delta1 ≲ †\delta2 ⇒ Γ
        (sub @ Data(_), Dead(DeadTy::Data(sup))) => {
            subty_check(kind_ctx, ty_ctx, sub, &Data(sup.clone()))
        }
        // Δ; Γ ⊢ τ1 ≲ τ3 ⇒ Γ''
        // TODO case missing. needed?
        _ => panic!("Good error message not implemented yet."),
    }
}
// ρ1 outlives ρ2 under Δ and Γ, producing Γ′
// Δ; Γ ⊢ ρ1 :> ρ2 ⇒ Γ′
fn outlives(
    kind_ctx: &KindCtx,
    ty_ctx: &TypingCtx,
    longer_prv: &Provenance,
    shorter_prv: &Provenance,
) -> Result<TypingCtx, String> {
    panic!("Not yet implemented.")
}

// Δ; Γ ⊢ List[ρ1 :> ρ2] ⇒ Γ′
fn multiple_outlives(
    kind_ctx: KindCtx,
    ty_ctx: TypingCtx,
    prv_rels: Vec<PrvRel>,
) -> Result<TypingCtx, String> {
    panic!("Not yet implemented.")
}

//
// Ownership Safety
//
//p is ω-safe under δ and γ, with reborrow exclusion list π , and may point to any of the loans in ωp
fn borrowable(
    kind_ctx: KindCtx,
    ty_ctx: TypingCtx,
    excl_reborrs: Vec<Place>,
    own: Ownership,
    p: PlaceExpr,
) -> Result<Vec<Loan>, String> {
    panic!("Not yet implemented.")
}
