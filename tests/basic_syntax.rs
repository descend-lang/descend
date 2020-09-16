#![cfg(test)]

extern crate descend;

use descend::ast::Ownership::{Shrd, Uniq};
use descend::dsl::*;
use descend::nat::*;
use descend::ty::Memory::{GpuGlobal, GpuShared};
use descend::ty::*;
use descend::{arr, tuple, tuple_dty};

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
    let _e =
        let_const("x", &i32, lit(&5),
        let_const("y", &i32, var("x"),
                  let_const("z", &i32, var("x"),
                            unit())));
}

#[test]
#[rustfmt::skip]
fn array_move_example() {
    // let x: 5.i32 = [1, 2, 3, 4, 5];
    // let y: 5.i32 = x;
    // let z: 5.i32 = x; // Error
    //
    //      desugared:
    // let const x: 5.i32 = [1, 2, 3, 4, 5];
    // let const y: 5.i32 = x;
    // let const z: 5.i32 = x; // Error
    // ()
    let_const("x", &arr_dty(5, &i32), arr![1, 2, 3, 4, 5],
    let_const("y", &arr_dty(5, &i32), var("x"),
              let_const("z", &arr_dty(5, &i32), var("x"),
                        unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn tuple_move_example() {
    // let x: i32 x f32 = (1, 2.0f32);
    // let y: i32 x f32 = x;
    // let z: i32 x f32 = x; // Error 
    //
    //      desugared:
    // let const x: i32 x f32 = (1, 2.0f32);
    // let const y: i32 x f32 = x;
    // let const z: i32 x f32 = x; // Error
    // ()
    let_const("x", &tuple_dty!(&i32, &f32), tuple!(1, 2.0f32),
    let_const("y", &tuple_dty!(&i32, &f32), var("x"),
              let_const("z", &tuple_dty!(&i32, &f32), var("x"),
                        unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_move_example() {
    // let x: i32 @ gpu.global = copy_to_gpumem(5);
    // let y: i32 @ gpu.global = x;
    // let z: i32 @ gpu.global = x; // Error
    //
    //      desugared:
    // let const x: i32 @ gpu.global = copy_to_gpumem<i32>(5);
    // let const y: i32 @ gpu.global = x;
    // let const z: i32 @ gpu.global = x; // Error
    // ()
    use Memory::GpuGlobal;

    let_const("x", &at_dty(&i32, &GpuGlobal),
              app(ddep_app(var("copy_to_gpumem"), &i32_dt), vec![lit(&5)]),
              let_const("y", &at_dty(&i32, &GpuGlobal), var("x"),
                        let_const("z", &at_dty(&i32, &GpuGlobal), var("x"),
                                  unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_borrow_example() {
    // let x: i32 @ gpu.global = copy_to_gpumem(5);
    // let y: &a mut gpu.global i32 = &mut x;
    // let z: i32 @ gpu.global = x; // Error
    // // do_something(y);
    //
    //      desugared:
    // let const x: i32 @ gpu.global = copy_to_gpumem<i32>(5);
    // let const y: &r uniq gpu.global i32 = &r uniq x;
    // let const z: i32 @ gpu.global = x; // Error
    // // do_something(y);
    // ()
    use Memory::GpuGlobal;

    let l = &prv("r");
    let_const("x", &at_dty(&i32, &GpuGlobal),
              app(ddep_app(var("copy_to_gpumem"), &i32_dt), vec![lit(&5)]),
              let_const("y", &ref_dty(l, Uniq, &GpuGlobal, &i32),
                        borr(l, Uniq, var("x")),
                        let_const("z", &at_dty(&i32, &GpuGlobal), var("x"),
                                  unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_immediate_borrow_example() {
    // let x: &a const gpu.global i32 = &const copy_to_gpumem(5);
    //
    //      desugared:
    // let const tmp: i32 @ gpu.global =
    //      copy_to_gpumem<i32>(5);
    // let const x: &r const gpu.global i32 = &r const tmp;
    // ()
    use Memory::GpuGlobal;

    let r = &prv("r");
    let_const("tmp", &at_dty(&i32, &GpuGlobal),
              app(ddep_app(var("copy_to_gpumem"), &i32_dt), vec![lit(&5)]),
              let_const("x", &ref_dty(r, Uniq, &GpuGlobal, &i32),
                        borr(r, Uniq, var("tmp")),
                        unit()));
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

    let r = &prv("r");
    let_const("x", &ref_dty(r, Uniq, &GpuGlobal, &i32),
              borr(r, Uniq, var("g")),
              let_const("y", &ref_dty(r, Uniq, &GpuGlobal, &i32),
                        var("x"),
                        let_const("z", &ref_dty(&r, Uniq, &GpuGlobal, &i32),
                                  var("x"),
                                  unit())));

    panic!("This shouldn't type check.")
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
    let_const("x", &ref_dty(r, Shrd, &GpuGlobal, &i32),
              borr(r, Shrd, var("g")),
              let_const("y", &ref_dty(r, Shrd, &GpuGlobal, &i32),
                        var("x"),
                        let_const("z", &ref_dty(r, Shrd, &GpuGlobal, &i32),
                                  var("x"),
                                  unit())));
}

#[test]
#[rustfmt::skip]
fn function_app_copy_example() {
    // let x: i32 = 5;
    // //f: (i32) ->[host] i32
    // f(x);
    // let y: i32 = x;
    //
    //      desugared:
    // let const x: un i32 = 5;
    // (f(x);
    // let const y: un i32 = x;
    // ())
    let_const("x", &i32, lit(&5),
    seq(
        app(var("f"), vec![var("x")]),
        let_const("y", &i32, var("x"),
                  unit())
    ));
}

#[test]
#[rustfmt::skip]
fn function_app_move_example() {
    // let x: 3.i32 = [1, 2, 3];
    // //f: (3.i32) ->[host] i32
    // f(x);
    // let y: 3.i32 = x; // Error
    //
    //      desugared:
    // let const x: 3.i32 = [1, 2, 3];
    // (f(x);
    // let const y: 3.i32 = x; // Error
    // ())
    let_const("x", &arr_dty(3, &i32), arr![1, 2, 3],
    seq(
        app(var("f"), vec![var("x")]),
        let_const("y", &arr_dty(3, &i32),
                  var("x"),
                  unit())
    ));

    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn function_app_borrow_example() {
    // let mut x: 3.i32 = [1, 2, 3];
    // //f: (&uniq 3.i32) ->[host] i32
    // f(&uniq x);
    // let mut y: 3.i32 = x;
    //
    //      desugared:
    // let mut x: 3.i32 = [1, 2, 3];
    // //f: r:prv => (&r mut 3.i32) ->[host] i32
    // (f<a>(&a mut x);
    // let mut y: 3.i32 = x;
    // ())
    let a = &prv("a");
    let_mut("x", &arr_dty(3, &i32), arr![1, 2, 3],
    seq(
        app(
            pdep_app(var("f"), a),
            vec![borr(a, Uniq, var("x"))]),
        let_mut("y", &arr_dty(3, &i32), var("x"),
                unit())
    ));
}

#[test]
#[rustfmt::skip]
fn function_app_move_attype_example() {
    // let x: 3.i32 @ gpu.global = copy_to_gpumem(&[1, 2, 3]);
    // // f: (3.i32) @ gpu.global ->[host] i32
    // f(x);
    // let y: 3.i32 @ gpu.global = x; // Error
    //
    //      desugared:
    // let const tmp: 3.i32 = [1, 2, 3];
    // let const x: 3.i32 @ gpu.global =
    //      copy_to_gpumem<3.i32><a>(&tmp);
    // (f(x);
    // let const y: 3.i32 @ gpu.global = x; // Error
    // ())
    use Memory::GpuGlobal;

    let a = &prv("a");
    let_const("tmp", &arr_dty(3, &i32), arr![1, 2, 3],
    let_const("x", &at_dty(&arr_dty(3, &i32), &GpuGlobal),
        ddep_app(
            pdep_app(
                app(var("copy_to_gpumem"),
                    vec![var("x")]),
                a),
            &arr_dty(3, &i32)),
    seq(
        app(var("f"), vec![var("x")]),
        let_const("y", &at_dty(&arr_dty(3, &i32), &GpuGlobal), var("x"),
                  unit())
    )));

    panic!("This should not type check.")
}

#[test]
#[rustfmt::skip]
fn function_decl_no_params_example() {
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
    
    fdecl("host_f", vec![], vec![], &unit_dty, &FrameExpr::FrTy(vec![]),
          CpuThread, vec![],

          let_const("x", &i32, lit(&5),
                  unit())
    );
}

#[test]
#[rustfmt::skip]
fn function_decl_params_example() {
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

    fdecl("gpu_thread_f", vec![], vec![("p1", &i32), ("p2", &i32)],
          &unit_dty, &FrameExpr::FrTy(vec![]), GpuThread, vec![],

          let_const("x", &i32, add(var("p1"), var("p2")),
                  unit())
    );
}

#[test]
#[rustfmt::skip]
fn function_decl_reference_params_example() {
    // fn gpu_group_f(p1: &gpu.shared i32, p2: &uniq gpu.global 3.i32) ->[gpu.group] () {
    //    let x: i32 = *p1 + *p2[0];
    // }
    //
    //      desugared:
    // fn gpu_group_f<'r1: life, 'r2: life>(
    //   p1: &'r1 shrd gpu.shared i32,
    //   p2: &'r2 uniq gpu.global 3.i32
    // ) ->[gpu.group] () {
    //   let const x: i32 = *p1 + *p2[0];
    //   ()
    // }
    use ExecLoc::GpuGroup;

    let r1 = prov_ident("'r1");
    let r2 = prov_ident("'r2");
    fdecl("gpu_group_f",
          vec![r1.clone(), r2.clone()],
          vec![("p1",
                &ref_dty(&Provenance::Ident(r1), Shrd, &GpuShared, &i32)),
               ("p2",
                &ref_dty(&Provenance::Ident(r2), Uniq, &GpuGlobal,
                         &at_dty(&arr_dty(3, &i32), &GpuGlobal)))],
          &unit_dty,
          &FrameExpr::FrTy(vec![]),
          GpuGroup,
          vec![],

          let_const("x", &i32,
                    add(deref(var("p1")), index(deref(var("p2")), Nat::Lit(0))),
                    unit())
    );
}
