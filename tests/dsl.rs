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
    // let const x: un i32 = 5;
    // let const y: un i32 = x;
    // let const z: un i32 = x;
    // ()
    let _e =
        let_const("x", &i32, lit(&5),
        let_const("y", &i32, ident("x"),
        let_const("z", &i32, ident("x"),
        unit())));
}

#[test]
#[rustfmt::skip]
fn array_move_example() {
    // let x: 5.i32 = [1, 2, 3, 4, 5];
    // let y: 5.i32 = x;
    // let z: 5.i32 = a; // Error
    //
    //      desugared:
    // let const x: aff 5.i32 = [1, 2, 3, 4, 5];
    // let const y: aff 5.i32 = x;
    // let const z: aff 5.i32 = x; // Error
    // ()
    let_const("x", &arr_ty(5, &i32), arr![1, 2, 3, 4, 5],
    let_const("y", &arr_ty(5, &i32), ident("x"),
    let_const("z", &arr_ty(5, &i32), ident("z"),
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
    // let const x: aff i32 x f32 = (1, 2.0f32);
    // let const y: aff i32 x f32 = x;
    // let const z: aff i32 x f32 = x; // Error
    // ()
    let_const("x", &tuple_ty!(&i32, &f32), tuple!(1, 2.0f32),
    let_const("y", &tuple_ty!(&i32, &f32), ident("x"),
    let_const("z", &tuple_ty!(&i32, &f32), ident("x"),
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
    // let const x: aff i32 + gpu.global = copy_to_gpumem<un i32>(5);
    // let const y: aff i32 + gpu.global = x;
    // let const z: aff i32 + gpu.global = x; // Error
    // ()
    use Memory::GpuGlobal;
    
    let_const("x", &own_ty(&i32, GpuGlobal),
        app(ddep_app(ident("copy_to_gpumem"), &i32_dt), lit(&5)),
    let_const("y", &own_ty(&i32, GpuGlobal), ident("x"),
    let_const("z", &own_ty(&i32, GpuGlobal), ident("x"),
    unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_borrow_example() {
    // let x: i32 + gpu.global = copy_to_gpumem(5);
    // let y: &'a uniq gpu.global i32 = &uniq x;
    // let z: i32 + gpu.global = x; // Error
    // // do_something(y);
    //
    //      desugared:
    // let const x: aff i32 + gpu.global = copy_to_gpumem<un i32>(5);
    // let const y: aff &'a mut gpu.global i32 = &'a mut x;
    // let const z: aff i32 + gpu.global = x; // Error
    // // do_something(y);
    // ()
    use Memory::GpuGlobal;
    
    let_const("x", &own_ty(&i32, GpuGlobal),
        app(ddep_app(ident("copy_to_gpumem"), &i32_dt), lit(&5)),
    let_const("y", &refm_ty(&life("a"), GpuGlobal, &i32),
        borr(&life("a"), mutable, ident("x")),
    let_const("z", &own_ty(&i32, GpuGlobal), ident("x"),
    unit())));
    
    panic!("This shouldn't type check.")
}

#[test]
#[rustfmt::skip]
fn gpu_memory_alloc_immediate_borrow_example() {
    // let x: &'a const gpu.global i32 = &const copy_to_gpumem(5);
    //
    //      desugared:
    // let const x: un &'a const gpu.global i32 =
    //     &'a const copy_to_gpumem<un i32>(5);
    // ()
    use Memory::GpuGlobal;
    
    let_const("x", &refc_ty(&life("a"), GpuGlobal, &i32),
        borr(&life("a"), constant,
             app(ddep_app(ident("copy_to_gpumem"), &i32_dt), lit(&5))),
    unit());
}

#[test]
#[rustfmt::skip]
fn mut_ref_movement_example() {
    // let x: &'a mut gpu.global i32 = &mut g;
    // let y: &'a mut gpu.global i32 = x;
    // let z: &'a mut gpu.global i32 = x; // Error
    //
    //      desugared:
    // let const x: aff &'a mut gpu.global i32 = &'a mut g;
    // let const y: aff &'a mut gpu.global i32 = x;
    // let const z: aff &'a mut gpu.global i32 = x; //Error
    // ()
    use Memory::GpuGlobal;
    
    let_const("x", &refm_ty(&life("a"), GpuGlobal, &i32),
        borr(&life("a"), mutable, ident("g")),
    let_const("y", &refm_ty(&life("a"), GpuGlobal, &i32),
        ident("x"),
    let_const("z", &refm_ty(&life("a"), GpuGlobal, &i32),
        ident("x"),
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
    // let const x: un &'a const gpu.global i32 = &'a const g;
    // let const y: un &'a const gpu.global i32 = x;
    // let const z: un &'a const gpu.global i32 = x;
    // ()
    use Memory::GpuGlobal;

    let_const("x", &refc_ty(&life("a"), GpuGlobal, &i32),
        borr(&life("a"), constant, ident("g")),
    let_const("y", &refc_ty(&life("a"), GpuGlobal, &i32),
        ident("x"),
    let_const("z", &refc_ty(&life("a"), GpuGlobal, &i32),
        ident("x"),
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
        app(ident("f"), ident("x")),
        let_const("y", &i32, ident("x"),
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
    // let const x: aff 3.i32 = [1, 2, 3];
    // (f(x);
    // let const y: aff 3.i32 = x; // Error
    // ())
    let_const("x", &arr_ty(3, &i32), arr![1, 2, 3],
    seq(
        app(ident("f"), ident("x")),
        let_const("y", &arr_ty(3, &i32),
            ident("x"),
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
    // let mut x: aff 3.i32 = [1, 2, 3];
    // (f<'a>(&'a mut x);
    // let mut y: aff 3.i32 = x;
    // ())
    let_mut("x", &arr_ty(3, &i32), arr![1, 2, 3],
    seq(
        app(
            ldep_app(ident("f"), &life("a")),
            borr(&life("a"), mutable, ident("x"))),
        let_mut("y", &arr_ty(3, &i32), ident("x"),
        unit())
    ));
}
