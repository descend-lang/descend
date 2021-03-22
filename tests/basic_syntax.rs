#![cfg(test)]

extern crate descend;

use descend::ty_check;

#[test]
#[ignore]
fn test_inplace_vector_add_fixed_sizes_inlined() -> Result<(), String> {
    let inplace_vector_add_fun = r#"fn inplace_vector_add<a: prv, b: prv>(
        ha_array: &a uniq cpu.heap [i32; 65536],
        hb_array: &b shrd cpu.heap [i32; 65536]
    ) -[cpu.thread]-> () {
        letprov <'r, 's, 'c, 'd, 'e, 'f, 'i, 'g, 'h> {
            let gpu: Gpu = gpu(0);

            let mut a_array: [i32; 65536] @ gpu.global =
            // TODO cpu.stack for the reborrow seems very wrong...
                gpu_alloc<'c, 'd, cpu.stack, cpu.stack, [i32; 65536]>(&'c uniq gpu, &'d shrd *ha_array);
            let b_array: [i32; 65536] @ gpu.global =
                gpu_alloc<'f, 'i, cpu.stack, cpu.stack, [i32; 65536]>(&'f uniq gpu, &'i shrd *hb_array);
            let grid: GridConfig<64, 1024> = spawn_threads<64, 1024, 'h, cpu.stack>(&'h shrd gpu);
            for t
            in
                zip(to_view_uniq(&'r uniq a_array), to_view(&'s shrd b_array))
            across grid {
                *t.0 = *t.0 + *t.1;
            }; //sync()
            copy_to_host<'g, a, [i32; 65536]>(&'g shrd a_array, ha_array);
        }
    }"#;

    let mut compil_unit = descend::parser::parse_unit(inplace_vector_add_fun).unwrap();
    if let Err(err) = ty_check::ty_check(&mut compil_unit) {
        panic!("{}", err)
    } else {
        let res_str = descend::codegen::gen(&compil_unit);
        print!("{}", res_str);
        Ok(())
    }
}

#[test]
fn test_inplace_vector_add() -> Result<(), String> {
    let inplace_vector_add_fun = r#"fn inplace_vector_add<n: nat, a: prv, b: prv>(
        ha_array: &a uniq cpu.heap [i32; n],
        hb_array: &b shrd cpu.heap [i32; n]
    ) -[cpu.thread]-> () {
        letprov <'r, 's, 'c, 'd, 'e, 'f, 'i, 'g, 'h> {
            let gpu: Gpu = gpu(0);

            let mut a_array: [i32; n] @ gpu.global =
            // TODO cpu.stack for the reborrow seems very wrong...
                gpu_alloc<'c, 'd, cpu.stack, cpu.stack, [i32; n]>(&'c uniq gpu, &'d shrd *ha_array);
            let b_array: [i32; n] @ gpu.global =
                gpu_alloc<'f, 'i, cpu.stack, cpu.stack, [i32; n]>(&'f uniq gpu, &'i shrd *hb_array);
            let view_a: [[&'r uniq gpu.global i32; n]] =
                to_view_mut<'r, gpu.global, n, i32>(&'r uniq a_array);
            let view_b: [[&'s shrd gpu.global i32; n]] =
                to_view<'s, gpu.global, n, i32>(&'s shrd b_array);
            let elems: [[(&'r uniq gpu.global i32, &'s shrd gpu.global i32); n]] =
                zip<n, &'r uniq gpu.global i32, &'s shrd gpu.global i32>(view_a, view_b);
            let grid: GridConfig<64, 1024> = spawn_threads<64, 1024, 'h, cpu.stack>(&'h shrd gpu);
            // hoisted runtime check: n == 64 * 1024
            for t in elems across grid {
                *t.0 = *t.0 + *t.1;
            }; //sync()
            copy_to_host<'g, a, [i32; n]>(&'g shrd a_array, ha_array);
        }
    }"#;

    let mut compil_unit = descend::parser::parse_unit(inplace_vector_add_fun).unwrap();
    if let Err(err) = ty_check::ty_check(&mut compil_unit) {
        panic!("{}", err)
    } else {
        let res_str = descend::codegen::gen(&compil_unit);
        print!("{}", res_str);
        Ok(())
    }
}

#[test]
fn test_inplace_vector_add_fixed_sizes() -> Result<(), String> {
    let inplace_vector_add_fun = r#"fn inplace_vector_add<a: prv, b: prv>(
        ha_array: &a uniq cpu.heap [i32; 65536],
        hb_array: &b shrd cpu.heap [i32; 65536]
    ) -[cpu.thread]-> () {
        letprov <'r, 's, 'c, 'd, 'e, 'f, 'i, 'g, 'h> {
            let gpu: Gpu = gpu(0);

            let mut a_array: [i32; 65536] @ gpu.global =
            // TODO cpu.stack for the reborrow seems very wrong...
                gpu_alloc<'c, 'd, cpu.stack, cpu.stack, [i32; 65536]>(&'c uniq gpu, &'d shrd *ha_array);
            let b_array: [i32; 65536] @ gpu.global =
                gpu_alloc<'f, 'i, cpu.stack, cpu.stack, [i32; 65536]>(&'f uniq gpu, &'i shrd *hb_array);
            let view_a: [[&'r uniq gpu.global i32; 65536]] =
                to_view_mut<'r, gpu.global, 65536, i32>(&'r uniq a_array);
            let view_b: [[&'s shrd gpu.global i32; 65536]] =
                to_view<'s, gpu.global, 65536, i32>(&'s shrd b_array);
            let elems: [[(&'r uniq gpu.global i32, &'s shrd gpu.global i32); 65536]] =
                zip<65536, &'r uniq gpu.global i32, &'s shrd gpu.global i32>(view_a, view_b);
            let grid: GridConfig<64, 1024> = spawn_threads<64, 1024, 'h, cpu.stack>(&'h shrd gpu);
            for t in elems across grid {
                *t.0 = *t.0 + *t.1;
            }; //sync()
            copy_to_host<'g, a, [i32; 65536]>(&'g shrd a_array, ha_array);
        }
    }"#;

    let mut compil_unit = descend::parser::parse_unit(inplace_vector_add_fun).unwrap();
    if let Err(err) = ty_check::ty_check(&mut compil_unit) {
        panic!("{}", err)
    } else {
        let res_str = descend::codegen::gen(&compil_unit);
        print!("{}", res_str);
        Ok(())
    }
}

#[test]
fn test_scalar_mult() -> Result<(), String> {
    let sclar_mult_fun = r#"fn scalar_mult<a: prv>(
        h_array: &a uniq cpu.heap [i32; 4096]
    ) -[cpu.thread]-> () {
        let gpu: Gpu = gpu(0);
        
        letprov <'g, 'h, 'r, 'z> {
            let mut array: [i32; 4096] @ gpu.global =
            // TODO cpu.stack for the reborrow has to be wrong...
                gpu_alloc<'g, 'r, cpu.stack, cpu.stack, [i32; 4096]>(&'g uniq gpu, &'r shrd *h_array); 
            for
                elem
            in
                to_view_mut<'z, gpu.global, 4096, i32>(&'z uniq array)
            across
                spawn_threads<64, 64, 'h, cpu.stack>(&'h shrd gpu)
            {
                *elem = 5 * *elem;
            };
            copy_to_host<'h, a, [i32; 4096]>(&'h shrd array, h_array);
        }
    }"#;

    let mut compil_unit = descend::parser::parse_unit(sclar_mult_fun).unwrap();
    if let Err(err) = ty_check::ty_check(&mut compil_unit) {
        panic!("{}", err)
    } else {
        let res_str = descend::codegen::gen(&compil_unit);
        print!("{}", res_str);
        Ok(())
    }
}
#[test]
fn test_scalar_mult_no_type_annotation() -> Result<(), String> {
    let sclar_mult_fun = r#"fn scalar_mult<a: prv>(
        h_array: &a uniq cpu.heap [i32; 4096]
    ) -[cpu.thread]-> () {
        let gpu = gpu(0);
        
        letprov <'g, 'h, 'r, 'z> {
            let mut array =
                gpu_alloc<'g, 'r, cpu.stack, cpu.stack, [i32; 4096]>(&'g uniq gpu, &'r shrd *h_array); 
            let view =
                to_view_mut<'z, gpu.global, 4096, i32>(&'z uniq array);
            let grid = spawn_threads<64, 64, 'h, cpu.stack>(&'h shrd gpu);
            for elem in view across grid {
                *elem = 5 * *elem;
            };
            copy_to_host<'h, a, [i32; 4096]>(&'h shrd array, h_array);
        }
    }"#;

    let mut compil_unit = descend::parser::parse_unit(sclar_mult_fun).unwrap();
    if let Err(err) = ty_check::ty_check(&mut compil_unit) {
        panic!("{}", err)
    } else {
        let res_str = descend::codegen::gen(&compil_unit);
        print!("{}", res_str);
        Ok(())
    }
}
/*
#[test]
#[rustfmt::skip]
fn scalar_copy_example() {
    // let x: i32 = 5;
    // let y: i32 = x;
    // let z: i32 = x;
    //
    //      desugared:
    // let const x: i32 = 5;
    // let const y: i32 = x;
    // let const z: i32 = x;
    // ()
    let e =
        let_const("x", &i32, lit(&5),
        let_const("y", &i32, ident("x"),
                  let_const("z", &i32, ident("x"),
                            unit())));

    assert_ty_checks_empty_ctxs(e, &unit_ty);
}

#[test]
#[rustfmt::skip]
fn array_copy_example() {
    // let x: 5.i32 = [1, 2, 3, 4, 5];
    // let y: 5.i32 = x;
    // let z: 5.i32 = x;
    //
    //      desugared:
    // let const x: 5.i32 = [1, 2, 3, 4, 5];
    // let const y: 5.i32 = x;
    // let const z: 5.i32 = x;
    // ()
    let e =
        let_const("x", &arr_ty(Nat::Lit(5), &i32), arr![1, 2, 3, 4, 5],
        let_const("y", &arr_ty(Nat::Lit(5), &i32), ident("x"),
                  let_const("z", &arr_ty(Nat::Lit(5), &i32), ident("x"),
                            unit())));

    assert_ty_checks_empty_ctxs(e, &unit_ty);
}

#[test]
#[rustfmt::skip]
fn tuple_copy_example() {
    // let x: i32 x f32 = (1, 2.0f32);
    // let y: i32 x f32 = x;
    // let z: i32 x f32 = x;
    //
    //      desugared:
    // let const x: i32 x f32 = (1, 2.0f32);
    // let const y: i32 x f32 = x;
    // let const z: i32 x f32 = x;
    // ()
    let e =
        let_const("x", &tuple_ty!(&i32, &f32), tuple!(1, 2.0f32),
        let_const("y", &tuple_ty!(&i32, &f32), ident("x"),
                  let_const("z", &tuple_ty!(&i32, &f32), ident("x"),
                            unit())));

    assert_ty_checks_empty_ctxs(e, &unit_ty);
}

#[test]
#[rustfmt::skip]
fn at_type_fail_move_example() {
    // let y: i32 @ gpu.global = x;
    // let z: i32 @ gpu.global = x; // Error
    //
    //      desugared:
    // let const y: i32 @ gpu.global = x;
    // let const z: i32 @ gpu.global = x; // Error
    // ()
    use Memory::GpuGlobal;

    let mut e =
        let_const("y", &at_ty(&i32, &GpuGlobal), ident("x"),
                  let_const("z", &at_ty(&i32, &GpuGlobal), ident("x"),
                            unit()));

    let x = IdentTyped::new(Ident::new("x"), at_ty(&i32, &GpuGlobal));
    let gl_ctx = GlobalCtx::new();
    let kind_ctx = KindCtx::new();
    let ty_ctx = TyCtx::new().append_ident_typed(x);

    if ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e).is_ok() {
       panic!("Moving a value twice is forbidden and should not type check.")
    }
}

#[test]
#[rustfmt::skip]
fn at_type_move_example() {
    // let y: i32 @ gpu.global = x;
    // let z: i32 @ gpu.global = y;
    //
    //      desugared:
    // let const y: i32 @ gpu.global = x;
    // let const z: i32 @ gpu.global = y;
    // ()
    use Memory::GpuGlobal;

    let mut e =
        let_const("y", &at_ty(&i32, &GpuGlobal), ident("x"),
                  let_const("z", &at_ty(&i32, &GpuGlobal), ident("y"),
                            unit()));

    let x = IdentTyped::new(Ident::new("x"), at_ty(&i32, &GpuGlobal));
    let gl_ctx = GlobalCtx::new();
    let kind_ctx = KindCtx::new();
    let ty_ctx = TyCtx::new().append_ident_typed(x);

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
        panic!(msg)
    };
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_move_example() {
    // let x: i32 @ gpu.global = copy_to_gpu(5);
    // let y: i32 @ gpu.global = x;
    // let z: i32 @ gpu.global = y;
    //
    //      desugared:
    // let const x: i32 @ gpu.global = copy_to_gpu<i32>(5);
    // let const y: i32 @ gpu.global = x;
    // let const z: i32 @ gpu.global = y;
    // ()
    use Memory::GpuGlobal;

    let mut e =
        let_const("x", &at_ty(&i32, &GpuGlobal),
                  app(ddep_app(ident("copy_to_gpu"), &i32), vec![lit(&5)]),
                  let_const("y", &at_ty(&i32, &GpuGlobal), ident("x"),
                            let_const("z", &at_ty(&i32, &GpuGlobal), ident("y"),
                                      unit())));

    let gl_ctx = GlobalCtx::new();
    let kind_ctx = copy_to_gpu::kind_ctx();
    let ty_ctx = TyCtx::new().append_ident_typed(copy_to_gpu::decl_and_ty());

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e)  {
        panic!(msg)
    }
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_move_fail_example() {
    // let x: i32 @ gpu.global = copy_to_gpu(5);
    // let y: i32 @ gpu.global = x;
    // let z: i32 @ gpu.global = x; // Error
    //
    //      desugared:
    // let const x: i32 @ gpu.global = copy_to_gpu<i32>(5);
    // let const y: i32 @ gpu.global = x;
    // let const z: i32 @ gpu.global = x; // Error
    // ()
    use Memory::GpuGlobal;

    let mut e =
        let_const("x", &at_ty(&i32, &GpuGlobal),
                  app(ddep_app(ident("copy_to_gpu"), &i32), vec![lit(&5)]),
                  let_const("y", &at_ty(&i32, &GpuGlobal), ident("x"),
                            let_const("z", &at_ty(&i32, &GpuGlobal), ident("x"),
                                      unit())));

    let gl_ctx = GlobalCtx::new();
    let kind_ctx = copy_to_gpu::kind_ctx();
    let ty_ctx = TyCtx::new().append_ident_typed(copy_to_gpu::decl_and_ty());

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e)  {
        assert_eq!(msg, "Place was moved before.")
    } else {
        panic!("Moving a value twice is forbidden and should not type check.")
    }
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_borrow_example() {
    // let x: i32 @ gpu.global = copy_to_gpu(5);
    // &uniq x

    //      desugared:
    // let const x: i32 @ gpu.global = copy_to_gpu<i32>(5);
    // &r uniq x
    use Memory::GpuGlobal;

    let prv = &prv("r");
    let mut e =
        let_const("x", &at_ty(&i32, &GpuGlobal),
                  app(ddep_app(ident("copy_to_gpu"), &i32), vec![lit(&5)]),
                  borr(prv, Uniq, ident("x")));

    let gl_ctx = GlobalCtx::new();
    let kind_ctx = copy_to_gpu::kind_ctx();
    let prv_mapping = PrvMapping { prv: "r".to_string(), loans: HashSet::new() };
    let ty_ctx = TyCtx::new()
        .append_ident_typed(copy_to_gpu::decl_and_ty())
        .append_prv_mapping(prv_mapping);

    if ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e).is_ok() {
        match e.ty.unwrap() {
            Ty::Ref(Provenance::Value(r_prv), Uniq, GpuGlobal, r_ty)
                if r_prv == "r" => {
                match *r_ty {
                    Ty::Scalar(ScalarTy::I32) => {}
                    _ => panic!("Wrong type.")
                }
            }
            _ => panic!("Wrong type.")
        }
    } else {
        panic!("It should be possible to borrow from an at type.")
    }
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_move_after_borrow_fail_example() {
    // let x: i32 @ gpu.global = copy_to_gpu(5);
    // let y: &a mut gpu.global i32 = &mut x;
    // let z: i32 @ gpu.global = x; // Error
    // // do_something(y);
    //
    //      desugared:
    // let const x: i32 @ gpu.global = copy_to_gpu<i32>(5);
    // let const y: &r uniq gpu.global i32 = &r uniq x;
    // let const z: i32 @ gpu.global = x; // Error
    // // do_something(y);
    // ()
    use Memory::GpuGlobal;

    let prv = &prv("r");
    let mut e =
        let_const("x", &at_ty(&i32, &GpuGlobal),
                  app(ddep_app(ident("copy_to_gpu"), &i32), vec![lit(&5)]),
                  let_const("y", &ref_ty(prv, Uniq, &GpuGlobal, &i32), borr(prv, Uniq, ident("x")),
                            let_const("z", &at_ty(&i32, &GpuGlobal), ident("x"),
                                      unit())));

    let gl_ctx = GlobalCtx::new();
    let kind_ctx = copy_to_gpu::kind_ctx();
    let prv_mapping = PrvMapping { prv: "r".to_string(), loans: HashSet::new() };
    let ty_ctx = TyCtx::new()
        .append_ident_typed(copy_to_gpu::decl_and_ty())
        .append_prv_mapping(prv_mapping);

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
        assert_eq!(msg, "A borrow is being violated.")
    } else {
        panic!("Illegal move of borrowed value.")
    }
}

#[test]
#[rustfmt::skip]
fn gpu_mem_alloc_copy_shrd_ref_immediate_borrow_example() {
    // let x: &shrd gpu.global i32 = &shrd copy_to_gpu(5);
    // let y: &shrd gpu.global i32 = x;
    //
    //      desugared:
    // let tmp: i32 @ gpu.global = copy_to_gpu<i32>(5);
    // let x: &r shrd gpu.global i32 = &r shrd tmp;
    // let y: &r shrd gpu.global i32 = x;
    // ()
    use Memory::GpuGlobal;

    let prv = &prv("r");
    let mut e =
        let_const("tmp", &at_ty(&i32, &Memory::GpuGlobal),
                  app(ddep_app(ident("copy_to_gpu"), &i32), vec![lit(&5)]),
            let_const("x", &ref_ty(prv, Shrd, &GpuGlobal, &i32),
                      borr(prv, Shrd, ident("tmp")),
                let_const("y", &ref_ty(prv, Shrd, &GpuGlobal, &i32),
                    ident("x"),
                    unit())));

    let gl_ctx = GlobalCtx::new();
    let kind_ctx = copy_to_gpu::kind_ctx();
    let prv_mapping = PrvMapping { prv: "r".to_string(), loans: HashSet::new() };
    let ty_ctx = TyCtx::new()
        .append_ident_typed(copy_to_gpu::decl_and_ty())
        .append_prv_mapping(prv_mapping);

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
       panic!(msg)
    }
}

#[test]
#[rustfmt::skip]
fn uniq_ref_movement_example() {
    // let x: &r uniq gpu.global i32 = &uniq g;
    // let y: &r uniq gpu.global i32 = x;
    // let z: &r uniq gpu.global i32 = x; // Error
    //
    //      desugared:
    // let const x: &r uniq gpu.global i32 = &r uniq g;
    // let const y: &r uniq gpu.global i32 = x;
    // let const z: &r uniq gpu.global i32 = x; //Error
    // ()
    use Memory::GpuGlobal;

    let prv = &prv("r");
    let mut e =
        let_const("x", &ref_ty(prv, Uniq, &GpuGlobal, &i32),
                  borr(prv, Uniq, ident("g")),
                  let_const("y", &ref_ty(prv, Uniq, &GpuGlobal, &i32),
                            ident("x"),
                            let_const("z", &ref_ty(&prv, Uniq, &GpuGlobal, &i32),
                                      ident("x"),
                                      unit())));

    let gl_ctx = GlobalCtx::new();
    let kind_ctx = copy_to_gpu::kind_ctx();
    let prv_mapping = PrvMapping { prv: "r".to_string(), loans: HashSet::new() };
    let g = IdentTyped::new(Ident::new("g"), at_ty(&i32, &GpuGlobal));
    let ty_ctx = TyCtx::new().append_prv_mapping(prv_mapping).append_ident_typed(g);

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
        assert_eq!(msg, "Place was moved before.")
    } else {
        panic!("Illegal move of borrowed value.")
    }
}

#[test]
#[rustfmt::skip]
fn shrd_ref_copy_example() {
    // let x: &r shrd gpu.global i32 = &shrd g;
    // let y: &r shrd gpu.global i32 = x;
    // let z: &r shrd gpu.global i32 = x;
    //
    //      desugared:
    // let const x: &r shrd gpu.global i32 = &r shrd g;
    // let const y: &r shrd gpu.global i32 = x;
    // let const z: &r shrd gpu.global i32 = x;
    // ()
    use Memory::GpuGlobal;

    let r = &prv("r");
    let mut e =
        let_const("x", &ref_ty(r, Shrd, &GpuGlobal, &i32),
                  borr(r, Shrd, ident("g")),
                  let_const("y", &ref_ty(r, Shrd, &GpuGlobal, &i32),
                            ident("x"),
                            let_const("z", &ref_ty(r, Shrd, &GpuGlobal, &i32),
                                      ident("x"),
                                      unit())));

    let gl_ctx = GlobalCtx::new();
    let kind_ctx = copy_to_gpu::kind_ctx();
    let prv_mapping = PrvMapping { prv: "r".to_string(), loans: HashSet::new() };
    let g = IdentTyped::new(Ident::new("g"), at_ty(&i32, &GpuGlobal));
    let ty_ctx = TyCtx::new().append_prv_mapping(prv_mapping).append_ident_typed(g);

    if ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e).is_err() {
        panic!("Shared refernece should be copyable.");
    }
}

#[test]
#[rustfmt::skip]
fn function_app_copy_example() {
    // let x: i32 = 5;
    // //f: (i32) ->[cpu.thread] i32
    // f(x);
    // let y: i32 = x;
    //
    //      desugared:
    // let const x: un i32 = 5;
    // (f(x);
    // let const y: un i32 = x;
    // ())
    let mut e =
        let_const("x", &i32, lit(&5),
        seq(
            app(fun_name("f"), vec![ident("x")]),
            let_const("y", &i32, ident("x"),
                      unit())
        ));

    let f_decl = PreDeclaredGlobalFun{
        name: "f".to_string(),
        fun_ty: Ty::Fn(vec![i32.clone()], Box::new(FrameExpr::FrTy(FrameTyping::new())),
                       CpuThread, Box::new(i32.clone()))
    };
    let gl_ctx = GlobalCtx::new().append_items(vec![f_decl]);
    let kind_ctx = KindCtx::new();
    let ty_ctx = TyCtx::new();

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
        panic!(format!("Typechecking failed with:\n {}", msg));
    }
}

#[test]
#[rustfmt::skip]
fn function_app_copy_array_example() {
    // let x: 3.i32 = [1, 2, 3];
    // //f: (3.i32) ->[cpu.thread] i32
    // f(x);
    // let y: 3.i32 = x;
    //
    //      desugared:
    // let const x: 3.i32 = [1, 2, 3];
    // (f(x);
    // let const y: 3.i32 = x;
    // ())
    let mut e =
        let_const("x", &arr_ty(Nat::Lit(3), &i32), arr![1, 2, 3],
        seq(
            app(fun_name("f"), vec![ident("x")]),
            let_const("y", &arr_ty(Nat::Lit(3), &i32),
                      ident("x"),
                      unit())
        ));

    let f_decl = PreDeclaredGlobalFun{
        name: "f".to_string(),
        fun_ty: Ty::Fn(vec![arr_ty(Nat::Lit(3), &i32)],
                       Box::new(FrameExpr::FrTy(FrameTyping::new())),
                       CpuThread, Box::new(i32.clone()))
    };
    let gl_ctx = GlobalCtx::new().append_items(vec![f_decl]);
    let kind_ctx = KindCtx::new();
    let ty_ctx = TyCtx::new();

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
        panic!("{}", msg);
    }
}

// skip #[test]
#[rustfmt::skip]
fn function_app_move_attype_example() {
    // let x: 3.i32 @ gpu.global = copy_to_gpu(&[1, 2, 3]);
    // // f: (3.i32) @ gpu.global ->[host] i32
    // f(x);
    // let y: 3.i32 @ gpu.global = x; // Error
    //
    //      desugared:
    // let const tmp: 3.i32 = [1, 2, 3];
    // let const x: 3.i32 @ gpu.global =
    //      copy_to_gpu<3.i32><r>(&r shrd tmp);
    // (f(x);
    // let const y: 3.i32 @ gpu.global = x; // Error
    // ())
    use Memory::GpuGlobal;

    let r = &prv("r");
    let mut e =
        let_const("tmp", &arr_ty(Nat::Lit(3), &i32), arr![1, 2, 3],
        let_const("x", &at_ty(&arr_ty(Nat::Lit(3), &i32), &GpuGlobal),
                  ddep_app(pdep_app(
                      app(fun_name("copy_to_gpu"),
                    vec![ident("x")]),
                      r),
                           &arr_ty(Nat::Lit(3), &i32)),
        seq(
            app(fun_name("f"), vec![ident("x")]),
            let_const("y", &at_ty(&arr_ty(Nat::Lit(3), &i32), &GpuGlobal), ident("x"),
                      unit())
    )));

    let f_decl = PreDeclaredGlobalFun{
        name: "f".to_string(),
        fun_ty: Ty::Fn(vec![arr_ty(Nat::Lit(3), &i32)],
                       Box::new(FrameExpr::FrTy(FrameTyping::new())),
                       CpuThread, Box::new(i32.clone()))
    };
    let copy_to_gpu_id_ty = copy_to_gpu::decl_and_ty();
    let copy_to_gpu_gl_f = PreDeclaredGlobalFun{
        name: copy_to_gpu_id_ty.ident.name,
        fun_ty: copy_to_gpu_id_ty.ty,
    };
    let gl_ctx = GlobalCtx::new().append_items(vec![f_decl, copy_to_gpu_gl_f]);
    let kind_ctx = KindCtx::new();
    let prv_mapping = PrvMapping { prv: "r".to_string(), loans: HashSet::new() };
    let ty_ctx = TyCtx::new().append_prv_mapping(prv_mapping);

    if let Err(msg) = ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
        panic!(msg);
    }
}

fn assert_ty_checks_empty_ctxs(mut e: Expr, expected_ty: &Ty) {
    let gl_ctx = GlobalCtx::new();
    let kind_ctx = KindCtx::new();
    let ty_ctx = TyCtx::new();
    match ty_check_expr(&gl_ctx, &kind_ctx, ty_ctx, ExecLoc::CpuThread, &mut e) {
        Ok(res_ty_ctx) => {
            assert_eq!(
                expected_ty,
                e.ty.as_ref().unwrap(),
                "Did not find expected type."
            );
            assert_eq!(
                &TyCtx::new(),
                &res_ty_ctx,
                "Input and output typing contexts should be the same."
            )
        }
        Err(msg) => panic!(format!("Failure due to {}", msg)),
    };
}

#[test]
#[rustfmt::skip]
fn function_def_no_params_example() {
    // fn host_f() ->[cpu.thread] () {
    //   let x: i32 = 5;
    //   ()
    // }
    //
    //      desugared:
    // fn host_f<>() ->[cpu.thread] () {
    //   let const x: un i32 = 5;
    //   ()
    // }
    use ExecLoc::CpuThread;

    let host_f =
        fdef("host_f", vec![], vec![], &unit_ty, CpuThread, vec![],
            let_const("x", &i32, lit(&5),
            unit())
        );
    let mut program = GlobalCtx::new().append_items(vec![host_f]);

    assert!(ty_check(&mut program).is_ok());
    assert_eq!(
        program.fun_defs_mut().next().unwrap().body_expr.ty.as_ref().unwrap(),
        &Ty::Scalar(ScalarTy::Unit)
    );
}

#[test]
#[rustfmt::skip]
fn function_def_params_example() {
    // fn gpu_thread_f(p1: i32, p2: i32) ->[gpu.thread] () {
    //   let x: i32 = p1 + p2;
    // }
    //
    //      desugared:
    // fn gpu_thread_f<>(p1: i32, p2: i32) ->[gpu.thread] () {
    //   let const x: i32 = p1 + p2;
    //   ()
    // }
    use ExecLoc::GpuThread;

    let gpu_thread_f =
        fdef("gpu_thread_f", vec![], vec![("p1", &i32), ("p2", &i32)],
             &unit_ty, GpuThread, vec![],

            let_const("x", &i32, add(ident("p1"), ident("p2")),
                      unit())
    );

    let mut program = GlobalCtx::new().append_items(vec![gpu_thread_f]);

    assert!(ty_check(&mut program).is_ok());
    assert_eq!(
        program.fun_defs_mut().next().unwrap().body_expr.ty.as_ref().unwrap(),
        &Ty::Scalar(ScalarTy::Unit)
    );
}

#[test]
#[rustfmt::skip]
fn function_decl_reference_params_example() {
    // fn gpu_group_f(p1: &shrd gpu.shared i32, p2: 3.i32 @ gpu.global) ->[gpu.group] () {
    //    let x: i32 = *p1 + p2[0];
    // }
    //
    //      desugared:
    // fn gpu_group_f<'r1: life, 'r2: life>(
    //   p1: &'r1 shrd gpu.shared i32,
    //   p2: 3.i32 @ gpu.global
    // ) ->[gpu.group] () {
    //   let const x: i32 = *p1 + p2[0];
    //   ()
    // }
    use ExecLoc::GpuGroup;

    let gpu_group_f =
        fdef("gpu_group_f",
             vec![("'r1", Kind::Provenance), ("'r2", Kind::Provenance)],
             vec![("p1",
                    &ref_ty(&Provenance::Ident(Ident::new("'r1")), Shrd, &GpuShared, &i32)),
                   ("p2",
                    &at_ty(&arr_ty(Nat::Lit(3), &i32), &GpuGlobal))],
             &unit_ty,
             GpuGroup,
             vec![],

             let_const("x", &i32,
                       add(deref(ident("p1")), index(ident("p2"), Nat::Lit(0))),
                       unit())
    );

    let mut program = GlobalCtx::new().append_items(vec![gpu_group_f]);

    let ty_check_res = ty_check(&mut program);
    match ty_check_res {
        Ok(_) => (),
        Err(msg) => panic!("Test failed with: {}", msg),
    };
    assert_eq!(
        program.fun_defs_mut().next().unwrap().body_expr.ty.as_ref().unwrap(),
        &Ty::Scalar(ScalarTy::Unit)
    );
}

mod copy_to_gpu {
    use descend::ast::internal::{FrameExpr, FrameTyping, IdentTyped};
    use descend::ast::Memory::GpuGlobal;
    use descend::ast::*;
    use descend::ast::{ExecLoc, IdentKinded, Kind, Ty};
    use descend::dsl::*;
    use descend::ty_check::ctxs::KindCtx;

    pub fn ty_ident() -> IdentKinded {
        IdentKinded::new(&Ident::new("elem_ty"), Kind::Ty)
    }
    pub fn kind_ctx() -> KindCtx {
        KindCtx::new().append_idents(vec![ty_ident()])
    }
    pub fn decl_and_ty() -> IdentTyped {
        let fun_ret_ty = at_ty(&i32, &GpuGlobal);
        let fun_ty = fun_ty(
            vec![i32.clone()],
            &empty_frame_expr,
            ExecLoc::CpuThread,
            &fun_ret_ty,
        );
        let cp_gpu_ty = genfun_ty(&ty_ident(), &empty_frame_expr, ExecLoc::CpuThread, &fun_ty);
        IdentTyped::new(Ident::new("copy_to_gpu"), cp_gpu_ty)
    }
}
*/
