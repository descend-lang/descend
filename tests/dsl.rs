#![cfg(test)]

extern crate descend;

use descend::dsl::*;
use descend::types::Memory;
use descend::{arr, tuple, tuple_ty};

#[test]
#[rustfmt::skip]
fn scalar_copy_example() {
    // let x: i32 = 5;
    // let y: i32 = x;
    // let z: i32 = x;
    //
    //      desugared:
    // let const x_'a: un i32 = 5;
    // let const y_'a: un i32 = x_'a;
    // let const z_'a: un i32 = x_'a;
    // ()
    let a = life("'a");
    let _e =
        let_const("x", &a, &i32, lit(&5),
        let_const("y", &a, &i32, ident("x", &a),
        let_const("z", &a, &i32, ident("x", &a),
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
    // let const x_'a: aff 5.i32 = [1, 2, 3, 4, 5];
    // let const y_'a: aff 5.i32 = x_'a;
    // let const z_'a: aff 5.i32 = x_'a; // Error
    // ()
    let a = life("'a");
    let_const("x", &a, &arr_ty(5, &i32), arr![1, 2, 3, 4, 5],
    let_const("y", &a, &arr_ty(5, &i32), ident("x", &a),
    let_const("z", &a, &arr_ty(5, &i32), ident("x", &a),
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
    // let const x_'a: aff i32 x f32 = (1, 2.0f32);
    // let const y_'a: aff i32 x f32 = x_'a;
    // let const z_'a: aff i32 x f32 = x_'a; // Error
    // ()
    let a = life("'a");
    let_const("x", &a, &tuple_ty!(&i32, &f32), tuple!(1, 2.0f32),
    let_const("y", &a, &tuple_ty!(&i32, &f32), ident("x", &a),
    let_const("z", &a, &tuple_ty!(&i32, &f32), ident("x", &a),
    unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_move_example() {
    // let x: i32 + gpu.global = copy_to_gpumem(5);
    // let y: i32 + gpu.global = x;
    // let z: i32 + gpu.global = x; // Error
    //
    //      desugared:
    // let const x_'a: aff i32 @ gpu.global = copy_to_gpumem_'static<un i32>(5);
    // let const y_'a: aff i32 @ gpu.global = x_'a;
    // let const z_'a: aff i32 @ gpu.global = x_'a; // Error
    // ()
    use Memory::GpuGlobal;

    let a = life("'a");
    let_const("x", &a, &at_ty(&i32, GpuGlobal),
        app(ddep_app(ident("copy_to_gpumem", &life("'static")), &i32_dt), lit(&5)),
    let_const("y", &a, &at_ty(&i32, GpuGlobal), ident("x", &a),
    let_const("z", &a, &at_ty(&i32, GpuGlobal), ident("x", &a),
    unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_borrow_example() {
    // let x: i32 @ gpu.global = copy_to_gpumem(5);
    // let y: &'a mut gpu.global i32 = &mut x;
    // let z: i32 @ gpu.global = x; // Error
    // // do_something(y);
    //
    //      desugared:
    // let const x_'a: aff i32 @ gpu.global = copy_to_gpumem_'static<un i32>(5);
    // let const y_'a: aff &'a mut gpu.global i32 = &mut x_'a;
    // let const z_'a: aff i32 @ gpu.global = x_'a; // Error
    // // do_something_'static(y_'a);
    // ()
    use Memory::GpuGlobal;

    let a = life("'a");
    let_const("x", &a, &at_ty(&i32, GpuGlobal),
        app(ddep_app(ident("copy_to_gpumem", &life("'static")), &i32_dt), lit(&5)),
    let_const("y", &a, &ref_mutable_ty(&life("a"), GpuGlobal, &i32),
        borr(mutable, ident("x", &a)),
    let_const("z", &a, &at_ty(&i32, GpuGlobal), ident("x", &a),
    unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_immediate_borrow_example() {
    // let x: &'a const gpu.global i32 = &const copy_to_gpumem(5);
    //
    //      desugared:
    // let const tmp_'a: aff i32 @ gpu.global = copy_to_gpumem_'static<un i32>(5);
    // let const x_'a: un &'a const gpu.global i32 = &const tmp_'a;
    // ()
    use Memory::GpuGlobal;

    let a = life("'a");
    let_const("tmp", &a, &at_ty(&i32, GpuGlobal),
        app(ddep_app(ident("copy_to_gpumem", &life("'static")), &i32_dt), lit(&5)),
    let_const("x", &a, &ref_const_ty(&life("a"), GpuGlobal, &i32),
        borr(constant, ident("tmp", &a)),
    unit()));
}

#[test]
#[rustfmt::skip]
fn mut_ref_movement_example() {
    // let x: &'a mut gpu.global i32 = &mut g;
    // let y: &'a mut gpu.global i32 = x;
    // let z: &'a mut gpu.global i32 = x; // Error
    //
    //      desugared:
    // let const x_'a: aff &'b mut gpu.global i32 = &mut g_'b;
    // let const y_'a: aff &'b mut gpu.global i32 = x_'a;
    // let const z_'a: aff &'b mut gpu.global i32 = x_'a; //Error
    // ()
    use Memory::GpuGlobal;

    let a = life("'a");
    let b = life("'b");
    let_const("x", &a, &ref_mutable_ty(&a, GpuGlobal, &i32),
        borr(mutable, ident("g", &b)),
    let_const("y", &a, &ref_mutable_ty(&b, GpuGlobal, &i32),
        ident("x", &a),
    let_const("z", &a, &ref_mutable_ty(&b, GpuGlobal, &i32),
        ident("x", &a),
    unit())));

    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn const_ref_copy_example() {
    // let x: &'a const gpu.global i32 = &const g;
    // let y: &'a const gpu.global i32 = x;
    // let z: &'a const gpu.global i32 = x;
    //
    //      desugared:
    // let const x_'a: un &'b const gpu.global i32 = &const g_'b;
    // let const y_'a: un &'b const gpu.global i32 = x_'a;
    // let const z_'a: un &'b const gpu.global i32 = x_'a;
    // ()
    use Memory::GpuGlobal;

    let a = life("'a");
    let b = life("'b");
    let_const("x", &a, &ref_const_ty(&b, GpuGlobal, &i32),
        borr(constant, ident("g", &b)),
    let_const("y", &a, &ref_const_ty(&b, GpuGlobal, &i32),
        ident("x", &a),
    let_const("z", &a, &ref_const_ty(&b, GpuGlobal, &i32),
        ident("x", &a),
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
    // let const x_'a: un i32 = 5;
    // (f_'static(x_'a);
    // let const y_'a: un i32 = x_'a;
    // ())
    let a = life("a");
    let_const("x", &a, &i32, lit(&5),
    seq(
        app(ident("f", &life("'static")), ident("x", &a)),
        let_const("y", &a, &i32, ident("x", &a),
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
    // let const x_'a: aff 3.i32 = [1, 2, 3];
    // (f_'static(x_'a);
    // let const y_'a: aff 3.i32 = x_'a; // Error
    // ())
    let a = life("a");
    let_const("x", &a, &arr_ty(3, &i32), arr![1, 2, 3],
    seq(
        app(ident("f", &life("'static")), ident("x", &a)),
        let_const("y", &a, &arr_ty(3, &i32),
            ident("x", &a),
        unit())
    ));

    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn function_app_borrow_example() {
    // let mut x: 3.i32 = [1, 2, 3];
    // //f: (&mut 3.i32) ->[host] i32
    // f(&mut x);
    // let mut y: 3.i32 = x;
    //
    //      desugared:
    // let mut x_'a: aff 3.i32 = [1, 2, 3];
    // (f_'static<'a>(&mut x_'a);
    // let mut y_'a: aff 3.i32 = x_'a;
    // ())
    let a = life("a");
    let_mut("x", &a, &arr_ty(3, &i32), arr![1, 2, 3],
    seq(
        app(
            ldep_app(ident("f", &life("'static")), &a),
            borr(mutable, ident("x", &a))),
        let_mut("y", &a, &arr_ty(3, &i32), ident("x", &a),
        unit())
    ));
}
