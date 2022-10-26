#![cfg(test)]
use std::fs;
use std::process::Command;
extern crate descend;

const COMPILE_PATH_DIR: &'static str = "/tmp";
const DESCEND_HEADER_DIR: &'static str = "./cuda-examples";
const DESCEND_HEADER_NAME: &'static str = "descend.cuh";
const NVCC_COMPILE_COMMAND: &'static str = "nvcc -c";

fn assert_nvcc_compile(cuda_src: &str) {
    const TMP_FILE_NAME: &'static str = "descend_generated_cuda.cu";
    const NVCC_INSTALLED_CHECK_COMMAND: &'static str = "nvcc --version > /dev/null";
    const BASH_COMMAND: &'static str = "bash";

    if Command::new(BASH_COMMAND)
        .arg("-c")
        .arg(NVCC_INSTALLED_CHECK_COMMAND)
        .status()
        .is_ok()
    {
        fs::copy(
            format!("{}/{}", DESCEND_HEADER_DIR, DESCEND_HEADER_NAME),
            format!("{}/{}", COMPILE_PATH_DIR, DESCEND_HEADER_NAME),
        )
        .expect(&format!(
            "failed to copy header file from {}/{} to {}/{}",
            DESCEND_HEADER_DIR, DESCEND_HEADER_NAME, COMPILE_PATH_DIR, DESCEND_HEADER_NAME
        ));

        fs::write(format!("{}/{}", COMPILE_PATH_DIR, TMP_FILE_NAME), cuda_src).expect(&format!(
            "Unable to write cuda code to file {}/{}",
            COMPILE_PATH_DIR, TMP_FILE_NAME
        ));

        let nvcc_command_str = format!(
            "{} {}/{}",
            NVCC_COMPILE_COMMAND, COMPILE_PATH_DIR, TMP_FILE_NAME
        );
        let compile_sucess = Command::new(BASH_COMMAND)
            .arg("-c")
            .arg(&nvcc_command_str)
            .status()
            .expect(&format!(
                "failed to compile generated CUDA-code!\n{}",
                nvcc_command_str
            ))
            .success();

        if !compile_sucess {
            panic!("Failed to compile generated CUDA-Code!")
        }
    } else {
        println!(
            "{}",
            Command::new(NVCC_INSTALLED_CHECK_COMMAND).status().unwrap()
        );
        println!("WARNING could not compile generated CUDA-code cause a missing nvcc-installation")
    }
}

macro_rules! assert_compile {
    ($src: expr) => {
        let res = descend::compile_src($src);
        if let Err(error) = res {
            eprintln!("{}\n{:#?}", $src, error);
            panic!("Unexpected error while typechecking");
        } else {
            println!("{}", res.as_ref().unwrap());
            assert_nvcc_compile(res.as_ref().unwrap())
        }
    };
}

macro_rules! assert_err_compile {
    ($src: expr) => {
        let res = descend::compile_src($src);
        if let Ok(gen_code) = res {
            eprintln!("{}\n{}", $src, gen_code);
            panic!("This should not typecheck");
        }
    };
}

#[test]
fn test_struct_def() {
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_trait_def() {
    let src = r#"
    trait Equal {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Equal {
        //const magic_number: i32 = 42; //TODO const items
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        fn eq2(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_impl_def() {
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Equal {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Equal for Point {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    impl Equal for i32 {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            *self == *other
        }
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_method_call() {
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Equal {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    impl Equal for Point {}
    impl Point {
        fn foo(self) -[cpu.thread]-> Point {
            self
        }
    }
    fn bar() -[cpu.thread]-> () {
        let x = 3;
        let p = Point { x, y: 42 };
        let q = Point { y: 42, x: 43 }; //Make sure the order in the C++-Code is right
        let p2 = p.foo();
        let q2x = q.foo().x;
        let p3 = (&shrd p2).eq(&shrd p2);
        let p4 = Point::eq(&shrd p2, &shrd p2);
        let z = p2.x
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_default_trait_impl_fun_call() {
    let src = r#"
    trait Foo {
        fn foo() -[cpu.thread]-> i32 {
            42
        }
    }
    struct Bar;
    impl Foo for Bar {}
    fn mainf() -[cpu.thread]-> () {
        let bar = Bar {};
        let x = Bar::foo()
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_monomoprhisation() {
    let src = r#"
    trait Trait1 {}
    trait Trait2 {}
    trait Equal<X, Y> where X: Trait1 {
        fn new<Z>(z: Z) -[cpu.thread]-> i32 {
            let mut x: X;
            let mut y: Y;
            42
        }
    }
    struct Point<X, Y> where X: Trait2 {
        x: X,
        y: Y
    }
    impl<A, B, C> Equal<A, B> for Point<B, C> where A: Trait1 + Trait2, B: Trait2 {
        fn new<Z>(z: Z) -[cpu.thread]-> i32 {
            let mut a: A;
            let mut b: B;
            let p = Point { x: 42, y: 43 };
            foo::<i32>(p, true); //TODO infer generic
            42
        }
    }
    impl Trait1 for i32 {}
    impl Trait2 for i32 {}
    impl Trait1 for f64 {}
    impl Trait2 for f64 {}

    fn foo<X, Z, T>(t: T, z: Z) -[cpu.thread] -> i32 where X: Trait1, T: Equal<X, X> {
        T::new(z)
    }

    fn bar() -[cpu.thread]-> i32 {
        let p = Point { x: 4.0, y: 42 };
        foo(p, 42);
        let p2 = Point { x: 4, y: 42.0 };
        foo(p2, 42.5);
        let p3 = Point { x: 4, y: 42.0 };
        //It is not possible to call "Point::new" because
        //the generic argument for "A" cannot be inferred.
        //It is syntactically not possible to pass this generic arg
        //This seems also in Rust not possible
        //Point::<i32, i32>::new::<f64>(true);
        42
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_infer_trait_args() {
    let src = r#"
    trait Equal<T> {
        fn new<Z>(z: Z) -[cpu.thread]-> i32 {
            let mut t: T;
            42
        }
    }
    impl<T> Equal<T> for T {}

    fn foo<T>(t: T) -[cpu.thread] -> i32 {
        T::new(26)
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Equal<T> {
        fn new<Z>(z: Z) -[cpu.thread]-> i32 {
            let mut t: T;
            42
        }
    }
    impl<T, X> Equal<T> for X {}
    fn foo<X>(t: X) -[cpu.thread] -> i32 {
        X::new(t) //cannot infer "T"
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_fun_calls() {
    let src = r#"
    trait Equal {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> i32 {
            1
        }
    }
    trait SomeOtherTrait {}
    impl SomeOtherTrait for i32 {}
    struct Point<T> {
        x: T,
        y: T
    }
    impl<T> Equal for Point<T> where T: SomeOtherTrait {}
    fn fun_with_generics<T>(t: T) -[cpu.thread]-> () where T: Equal {
        let i1: i32 = (&shrd t).eq(&shrd t);
        let i2: i32 = T::eq(&shrd t, &shrd t)
    }
    fn fun_with_generics2<T>(t1: T, t2: T, t3: T, t4: T) -[cpu.thread]-> () where T: SomeOtherTrait  {
        let p: Point<T> = Point::<T> { x: t1, y: t2 };
        fun_with_generics(p);

        let p2 = Point { x: t3, y: t4 };
        (&shrd p2).eq(&shrd p2);
        Point<_>::eq(&shrd p2, &shrd p2);
        ()
    }
    fn bar() -[cpu.thread]-> () {
        fun_with_generics2(1, 2, 3, 4)
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Equal {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> i32 {
            1
        }
    }
    struct Point<T> {
        x: T,
        y: T
    }
    impl<T> Equal for Point<T> {} //here "T" has no constraints
    fn fun_with_generics<T>(t: T) -[cpu.thread]-> () where T: Equal {
        let i1: i32 = (&shrd t).eq(&shrd t);
        let i2: i32 = T::eq(&shrd t, &shrd t)
    }
    fn fun_with_generics2<T>(t1: T, t2: T, t3: T, t4: T) -[cpu.thread]-> () {
        let p: Point<T> = Point::<T> { x: t1, y: t2 };
        fun_with_generics(p);

        let p2: Point<T> = Point::<T> { x: t3, y: t4 };
        (&shrd p2).eq(&shrd p2);
        Point<_>::eq(&shrd p2, &shrd p2);
        ()
    }
    fn bar() -[cpu.thread]-> () {
        fun_with_generics2(1, 2, 3, 4)
    }
    "#;
    assert_compile!(src); //This generates other code because "T" is not monomorphised
}

#[test]
fn test_moved_struct_attribute() {
    let src = r#"
    struct Test<a: prv> {
        x: &a uniq cpu.mem i32
    }
    struct Point {
        x: Test,
        y: i32
    }
    fn bar() -[cpu.thread]-> () <'a>{
        let test = 42;
        let x = Test::<'a> { x: &'a uniq test };
        let p = Point { x, y: 42 };
        let z = p.x;
        let z2 = p.x //Already moved
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Test;
    struct Point {
        x: Test,
        y: i32
    }
    fn bar() -[cpu.thread]-> () {
        let x = Test {};
        let p = Point { x, y: 42 };
        let z = p.y;
        let z2 = p.y; //y is copyable
        ()
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test;
    struct Point {
        x: Test,
        y: i32
    }
    fn bar() -[cpu.thread]-> () {
        let x = Test {};
        let p = Point { x, y: 42 };
        let z = p.x;
        let z2 = p.x //x is not copyable
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Test;
    impl Copy for Test {}
    struct Point {
        x: Test,
        y: i32
    }
    fn bar() -[cpu.thread]-> () {
        let x = Test {};
        let p = Point { x, y: 42 };
        let z = p.x;
        let z2 = p.x //x is copyable
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_partitial_moved_struct() {
    let src = r#"
    struct Test;
    impl Copy for Test {}
    struct Point {
        x: Test,
        y: i32
    }
    impl Point {
        fn foo(self) -[cpu.thread]-> Point {
            self
        }
    }
    fn bar() -[cpu.thread]-> () {
        let x = Test {};
        let p = Point { x, y: 42 };
        let px = p.x;
        let p2 = p.foo()
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test;
    struct Point {
        x: Test,
        y: i32
    }
    impl Point {
        fn foo(self) -[cpu.thread]-> Point {
            self
        }
    }
    fn bar() -[cpu.thread]-> () {
        let x = Test {};
        let p = Point { x, y: 42 };
        let px = p.x;
        let p2 = p.foo()
    }
    "#;
    assert_err_compile!(src);
}

#[test]
//TODO const-items
fn test_associated_const() {
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Equal {
        //const important_const: f32;
        //const PANIC: () = panic!("compile-time panic");
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Equal for Point {
        //const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    impl Equal for i32 {
        //const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            //let _ = PANIC;
            *self == *other
        }
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Equal {
        //const important_const: f32 = 4.2; // initialize with some value
        //const PANIC: () = panic!("compile-time panic");
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Equal for Point {
        //const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    impl Equal for i32 {
        //const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            //let _ = PANIC;
            *self == *other
        }
    }
    "#;
    assert_compile!(src);

    // let src = r#"
    // struct Point {
    //     x: i32,
    //     y: i32
    // }
    // trait Equal {
    //     //const important_const: f32;
    //     //const PANIC: () = panic!("compile-time panic");
    //     fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    // }
    // impl Equal for Point {
    //     //const important_const = 4.2;
    //     fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
    //         (*self).x == (*other).x && (*self).y == (*other).y
    //     }
    // }
    // impl Equal for i32 {
    //     //No definion of "important_const"
    //     fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
    //         //let _ = PANIC;
    //         self == other
    //     }
    // }
    // "#;
    // assert_err_compile!(src);
}

#[test]
fn test_unimplmented_method_impl_def() {
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Equal {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Equal for Point {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Equal {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        fn eq2(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            true
        }
    }
    impl Equal for Point {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Equal {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        fn eq2(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Equal for Point {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_multiple_gl_fun_with_same_name() {
    let src = r#"
    fn foo() -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo() -[cpu.thread]-> i32 {
        42
    }
    fn foo() -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_multiple_structs_with_same_name() {
    let src = r#"
    struct Test {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test {}
    struct Test {}
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_multiple_attributes_in_struct_with_same_name() {
    let src = r#"
    struct Test { x: i32, y: f32 }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test { x: i32, x: f32 }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_multiple_fun_params_in_struct_with_same_name() {
    let src = r#"
    fn foo(x: i32, y: f32) -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo(x: i32, x: f32) -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_multiple_ass_funs_with_same_name() {
    let src = r#"
    trait Test {
        fn foo(x: i32, y: f32) -[cpu.thread]-> () {
            ()
        }
        fn foo2(x: i32, y: f32) -[cpu.thread]-> ();
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Test {
        fn foo(x: i32, y: f32) -[cpu.thread]-> () {
            ()
        }
        fn foo(x: i32, y: f32) -[cpu.thread]-> ();
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_multiple_generics_with_same_name() {
    let src = r#"
    struct Test<m: nat, n: nat> { x: [i32; m], y: [f32; n] }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test<m: nat, m: nat> { x: [i32; m], y: [f32; m] }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_ambious_generic_struct_name() {
    let src = r#"
    struct T {}
    fn foo<X>(x: T, y: X) -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct T {}
    fn foo<T>(x: T, y: T) -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_invalid_type_in_fn() {
    let src = r#"
    struct T {}
    fn foo(x: T) -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct T {}
    fn foo(x: Ty) -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct T {}
    fn foo(x: X) -[cpu.thread]-> i32 {
        42
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_invalid_type_in_struct() {
    let src = r#"
    struct Test { x: i32, y: f32 }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test { x: i32, y: f42 }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_invalid_generic_in_trait() {
    let src = r#"
    trait Equal<T> {
        fn eq(&shrd cpu.mem self, T) -[cpu.thread]-> bool;
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Equal<i32> {
        fn eq(&shrd cpu.mem self, i32) -[cpu.thread]-> bool;
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_invalid_number_generics_struct() {
    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point::<i32, i32> { x: 16, y: 4 }
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point::<i32> { x: 16, y: 4 }
    }
    "#;
    assert_compile!(src); //Second generic param can be inferred

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point::<i32, i32, i32> { x: 16, y: 4 }
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_invalid_number_generics_trait() {
    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Equal<T> {}
    impl<T> Equal<T> for Point<i32, i32> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Equal<T> {}
    impl Equal<i32> for Point<i32, i32> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Equal<T> {}
    impl Equal for Point<i32, i32> {}
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Equal<T> {}
    impl Equal<> for Point<i32, i32> {}
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Equal<T> {}
    impl Equal<i32, f32> for Point<i32, i32> {}
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_invalid_generic_kind() {
    let src = r#"
    struct Point<X: dty, n: nat> {
        x: X,
        y: [i32; n]
    }
    trait Equal {}
    impl<T> Equal for Point<T, 42> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X: dty, n: nat> {
        x: X,
        y: [i32; n]
    }
    trait Equal {}
    impl<T, X: nat> Equal for Point<T, X> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X: ty, n: nat> {
        x: X,
        y: [i32; n]
    }
    trait Equal {}
    impl<T, X> Equal for Point<T, X> {}
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X: ty, n: nat> {
        x: X,
        y: [i32; n]
    }
    trait Equal {}
    impl<T: mem> Equal for Point<T, 42> {}
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_constraint_checker() {
    let src = r#"
    trait Trait1<A> {
        fn fun1(a: A) -[cpu.thread] -> i32;
    }
    trait Trait2<B> : Trait1<B> {
        fn fun2(a: B) -[cpu.thread] -> i32;
    }
    fn foo<X, A>(x: X, a: A) -[cpu.thread] -> i32 where X: Trait1<A> {
        X::fun1(a)
    }
    //In this two functions is X not constraint to implement Trait1, but because
    //Trait1 is a supertrait this can be inferred
    fn bar<X, A>(x: X, a: A, a2: A) -[cpu.thread] -> i32 where X: Trait2<A> {
        X::fun1(a);
        X::fun2(a2)
    }
    fn baz<X>(x: X) -[cpu.thread] -> i32 where X: Trait2<i32> {
        X::fun1(1);
        X::fun2(2)
    }
    "#;
    //This print some warnings because here is no codegen for foo, bar and baz possible
    assert_compile!(src);
}

#[test]
fn test_unfullfilled_constraints() {
    let src = r#"
    struct Struct1 { i: i32 }
    struct Struct2 { i: f32 }
    trait Equal {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    struct Point<X, Y> where X: Equal, Y:Equal {
        x: X,
        y: Y
    }
    impl Equal for Struct1 {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    fn foo() -[cpu.thread]-> () {
        let x: Struct1 = Struct1 { i: 42 };
        let y: Struct1 = Struct1 { i: 43 };
        let p: Point<Struct1, Struct1> = Point::<Struct1, Struct1> {x, y}
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Struct1 { i: i32 }
    struct Struct2 { i: i32 }
    trait Equal {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    struct Point<X, Y> where X: Equal, Y:Equal {
        x: X,
        y: Y
    }
    impl Equal for Struct1 {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    fn foo() -[cpu.thread]-> () {
        let x: Struct1 = Struct1 { i: 42 };
        let y: Struct2 = Struct2 { i: 43 };
        let p: Point<Struct1, Struct2> = Point<Struct1, Struct2> {x, y}
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_unfullfilled_constraints2() {
    let src = r#"
    trait Equal {
        fn foo(x: i32) -[cpu.thread]-> bool {
            false
        }
    }
    trait Ord: Equal {
        fn foo2(x: i32) -[cpu.thread]-> bool;
    }
    trait SOrd: Ord {
        fn foo3(x: i32) -[cpu.thread]-> bool;
    }
    struct Point<X, Y> where X: Equal, Y:Equal {
        x: X,
        y: Y
    }
    struct Point2<X, Y> where X: SOrd, Y: Ord {
        p: Point<X, Y>
    }
    "#;
    assert_compile!(src);

    //TODO cant pass ArgKinded with generic params
    // let src = r#"
    // trait Equal {
    //     fn foo(x: i32) -[cpu.thread]-> bool {
    //         false
    //     }
    // }
    // trait Ord: Equal {
    //     fn foo2(x: i32) -[cpu.thread]-> bool {false}
    // }
    // trait SOrd: Ord {
    //     fn foo3(x: i32) -[cpu.thread]-> bool {false}
    // }
    // struct Point<X, Y> where X: Equal, Y:Equal {
    //     x: X,
    //     y: Y
    // }
    // struct T<X> where X: Ord {}
    // struct Point2<Y> where Y: SOrd {
    //     p: Point<T<Y>, Y>
    // }
    // impl SOrd for T<X> where X: SOrd {}
    // "#;
    // assert_compile!(src);

    // let src = r#"
    // trait Equal {
    //     fn foo(x: i32) -[cpu.thread]-> bool {
    //         false
    //     }
    // }
    // trait Ord: Equal {
    //     fn foo2(x: i32) -[cpu.thread]-> bool {false}
    // }
    // trait SOrd: Ord {
    //     fn foo3(x: i32) -[cpu.thread]-> bool {false}
    // }
    // struct Point<X, Y> where X: Equal, Y:Equal {
    //     x: X,
    //     y: Y
    // }
    // struct T<X> where X: Ord {}
    // struct Point2<Y> where Y: Ord {
    //     p: Point<T<Y>, Y>
    // }
    // impl SOrd for T<X> where X: SOrd {}
    // "#;
    // assert_err_compile!(src);
}

#[test]
fn test_cylic_constraints() {
    let src = r#"
    trait MyTrait {}
    impl<T> MyTrait for T where T: MyTrait {}
    struct Point<X> where X: MyTrait {
        x: X
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point { x: 42 }
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_cyclic_struct_defs() {
    let src = r#"
    struct Point1 {
        x: i32,
        y: i32,
        p2: Point2,
        p3: Point2
    }
    struct Point2 {
        x: f32,
        y: f32
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point1 {
        x: i32,
        y: i32,
        p2: Point2
    }
    struct Point2 {
        x: f32,
        y: f32,
        p1: Point1
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct A {
        b: B
    }
    struct B {
        c: C
    }
    struct C {
        a: A
    }
    "#;
    assert_err_compile!(src);
}

#[ignore] //How to represent this in the AST?
#[test]
fn test_cyclic_struct_defs2() {
    let src = r#"
    struct A<a: prv> {
        b: &a uniq cpu.mem B
    }
    struct B<a: prv> {
        c: &a uniq cpu.mem C
    }
    struct C<a: prv> {
        a: &a uniq cpu.mem A
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_struct_with_lifetimes() {
    let src = r#"
    struct Test<a: prv> {
        x: &a uniq cpu.mem i32
    }
    impl<a: prv> Test<a> {
        fn bar(&shrd cpu.mem self, i: i32) -[cpu.thread]-> i32 {
            i + *((*self).x)
        }
    }
    fn test_double_reference(x: & uniq cpu.mem & uniq cpu.mem i32) -[cpu.thread]-> () {
        *(*x) = 42
    }
    fn test_double_reference2<a: prv>(x: &a uniq cpu.mem & uniq cpu.mem i32) -[cpu.thread]-> () {
        *(*x) = 42
    }
    fn test_double_reference3<a: prv, b: prv>(x: &a uniq cpu.mem &b uniq cpu.mem i32) -[cpu.thread]-> () {
        *(*x) = 42
    }
    fn foo<a: prv>(mut t: Test<a>) -[cpu.thread]-> i32 {
        *(t.x) = 42;
        (&shrd t).bar(15)
    }
    fn mainf() -[cpu.thread]-> () <'a>{
        let mut test: i32 = 1;
        let mut t = Test { x: &'a uniq test };
        foo(t);

        let mut test2 = 19;
        let mut t2 = Test { x: &uniq test2 };

        let mut test3 = 2;
        let mut test4 = &uniq test3;
        test_double_reference(&uniq test4);
        test_double_reference2(&uniq test4)
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_bin_op() {
    let src = r#"
    fn foo() -[gpu.thread]-> () {
        let x = 42;
        let y = 43;
        let z = x + y;
        let z2 = x
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T>(x: T, y: T) -[gpu.thread]-> () where T : Number {
        let z = x + y;
        let z2 = x
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T>(x: T, y: T) -[gpu.thread]-> () where T : Add<T, T> {
        let z = x + y
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T>(x: T, y: T) -[gpu.thread]-> () where T : Add<T, T> {
        let z = x + y;
        let z2 = x
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    fn foo() -[gpu.thread]-> () {
        let x = 42;
        let y = 43;
        let z = x == y;
        let z2 = x
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T>(x: T, y: T) -[gpu.thread]-> () where T : Number {
        let z = (x == y)
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T>(x: T, y: T) -[gpu.thread]-> () where T : Eq {
        let z = x == y
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T>(x: T, y: T) -[gpu.thread]-> () where T : Eq {
        let z = x + y;
        let z2 = x
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    fn foo<T>(x: T, y: T) -[gpu.thread]-> () where T : Eq + Copy {
        let z = x == y;
        let z2 = x
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_std_lib() {
    let src = r#"
    trait Eq {} //Already defined
    "#;
    assert_err_compile!(src);

    let src = r#"
    fn foo<T>(t1: T, t2: T) -[gpu.thread]-> () where T: Eq {
        ()
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T>(t1: i32, t2: i32) -[gpu.thread]-> () {
        let res = t1 == t2
    }
    "#;
    assert_compile!(src);

    //References to types which implements Eq and Copy are also allowed
    let src = r#"
    fn foo(t1: &shrd gpu.global i32, t2: &shrd gpu.global i32) -[gpu.thread]-> () {
        let res = t1 == t2
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo<T, m:mem>(t1: &shrd m T, t2: &shrd m T) -[gpu.thread]-> () where T: Eq + Copy {
        let res = (t1 == t2)
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_tuple_copy() {
    let src = r#"
    fn foo<T>(t1: T) -[gpu.thread]-> () where T: Copy {
        ()
    }
    fn bar() -[gpu.thread]-> () {
        let i1 = 42;
        let i2 = 43;
        foo((i1, i2))
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_lambda() {
    //Simple lambda fun for addition should not compile because
    //the types of x and y can not be inferred
    //The let-statement itself should typecheck because we use implicit
    //type identifiers $Y and $Y for the types of x and y and infer
    //$X and $Y implements the "Add"-Trait
    let src = r#"
    fn mainf() -[gpu.thread]-> () {
        let add = |x, y| -[gpu.thread]-> _ {
            x + y
        }
    }
    "#;
    assert_err_compile!(src);

    //if we call the lambda fun with two i32-dtys $X and $Y can be inferred
    let src = r#"
    fn mainf() -[gpu.thread]-> () {
        let add = |x, y| -[gpu.thread]-> _ {
            x + y
        };
        let x = add(42, 14)
    }
    "#;
    assert_compile!(src);

    //Same with two f64-dtys
    let src = r#"
    fn mainf() -[gpu.thread]-> () {
        let add = |x, y| -[gpu.thread]-> _ {
            x + y
        };
        let y = add(13.0, 15.0)
    }
    "#;
    assert_compile!(src);

    //Adding an i32 is sufficient to infer all types
    let src = r#"
    fn mainf() -[gpu.thread]-> () {
        let add = |x, y| -[gpu.thread]-> _ {
            let z = x + y;
            (1 + z) + x
        }
    }
    "#;
    assert_compile!(src);

    //This does not compile because we can only infer $Z implements Add<i32, $OUTPUT>
    let src = r#"
    fn mainf() -[gpu.thread]-> () {
        let add = |x, y| -[gpu.thread]-> _ {
            let z = x + y;
            (z + 1) + x
        }
    }
    "#;
    assert_err_compile!(src);

    //Before reaching "let y = ...", this should typecheck
    //But then $X and $Y have been inferred as i32. So its
    //not allowed to add two f64-dtys
    let src = r#"
    fn mainf() -[gpu.thread]-> () {
        let add = |x, y| -[gpu.thread]-> _ {
            x + y
        };
        let x = add(42, 14);
        let y = add(13.0, 15.0)
    }
    "#;
    assert_err_compile!(src);

    //We can do the same also with references instead of values
    let src = r#"
    fn mainf(x: &shrd gpu.global i32, y: &shrd gpu.global i32, res: &uniq gpu.global i32) -[gpu.thread]-> () {
        let add = |x, y, res| -[gpu.thread]-> () {
            *res = *x + *y
        };
        let y = add(x, y, res)
    }
    "#;
    assert_compile!(src);

    //We can also use structs for addition
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    impl Add<Point, Point> for Point {
        fn add(self, other: Self) -[gpu.thread]-> Self {
            Point {
                x: self.x + other.x,
                y: self.y + other.y
            }
        }
    }
    impl Copy for Point {}
    fn mainf(x: &shrd gpu.global Point, y: &shrd gpu.global Point, res: &uniq gpu.global Point) -[gpu.thread]-> () {
        let add = |x, y, res| -[gpu.thread]-> _ {
            *res = *x + *y
        };
        let y = add(x, y, res)
    }
    "#;
    assert_compile!(src);

    //But if the custom do not implement copy this does not compile
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    impl Add<Point, Point> for Point {
        fn add(self, other: Self) -[gpu.thread]-> Self {
            Point {
                x: self.x + other.x,
                y: self.y + other.y
            }
        }
    }
    fn mainf(x: &shrd gpu.global Point, y: &shrd gpu.global Point, res: &uniq gpu.global Point) -[gpu.thread]-> () {
        let add = |x, y, res| -[gpu.thread]-> _ {
            *res = *x + *y
        };
        let y = add(x, y, res)
    }
    "#;
    assert_err_compile!(src);
}

#[test]
#[ignore] // TODO Reassignment to dead types dont work
fn test_struct_dead_types() {
    let src = r#"
    struct Test<a: prv, m: mem> {
        test: &a uniq m i32
    }
    fn foo<m: mem>(a: &uniq m i32) -[cpu.thread]-> () {
        ()
    }
    fn test() -[cpu.thread]-> () {
        let mut x = 42;
        let mut x2 = x;
        let mut t = Test { test: &uniq x };
        foo(t.test);
        t.test = &uniq x2 //t.test is dead
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_lambda2() {
    let src = r#"
    struct Array<T, N: nat> {
        data: [T; N]
    }
    impl<T, N: nat> Array<T, N> {
        fn new_pair(t1: T, t2: T) -[gpu.thread]-> Array<T, 2> {
            Array {
                data: [t1, t2]
            }
        }
    }
    impl<T, N: nat, m: mem> Array<T, N> where T: Number {
        fn reduce(&shrd m self, zero: T) -[gpu.thread]-> T {
            let mut result = zero;
            for_nat i in range(0, N) {
                result = result + (*self).data[i]
            };
            result
        }
    }
    fn mainf(array_global: &shrd gpu.global Array<i32, 2>) -[gpu.thread]-> () {
        let red = |vec, zero| -[gpu.thread]-> _ {
            vec.reduce(zero)
            // This two spellings act identical as `vec.reduce(zero)`
            // Array<_, 2>::reduce(vec, zero)
            // Array<i32, 2>::reduce(vec, zero)
            //
            // `Array::reduce(vec, zero)` dont work in this case
            // because of the nat in the second component of `Array`
        };
        let array2 = Array<_, 2>::new_pair(16, 27);
        let res = red(array_global, 0)
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_different_generic_param_types() {
    let src = r#"
    trait Trait<T, m: mem> {
        fn getX(&uniq m self) -[gpu.thread]-> T;
    }
    struct Point<T> where T: Copy {
        x: T,
        y: T
    }
    struct Points<T: dty, n: nat, m: mem, a: prv> {
        points: [Point<T>; n],
        special_point: &a uniq m Point<i32>
    }
    impl<T> Copy for Point<T> {}
    impl<T, m: mem> Trait<T, m> for Point<T> where T: Number {
        fn getX(&uniq m self) -[gpu.thread]-> T {
            (*self).x
        }
    }
    impl<T, n: nat, a: prv> Points<T, n, gpu.global, a> where T: Copy {
        fn newPoint(self, t: T) -[gpu.thread]-> Point<T> {
            Point {
                x: t,
                y: t
            }
        }
    }
    fn mainf(p_global1: &uniq gpu.global Point<i32>,
            p_global2: &uniq gpu.global Point<i32>) -[gpu.thread]-> () {
        let x = 42;
        let y = 43;
        let p1 = Point {x, y};
        let p2 = Point {x: 42, y};
        let p3 = Point {x, y: 43};
        let p4 = Point {x: 42.2, y: 43.3};
        let points1 = Points { points: [p1, p2, p3], special_point: p_global1 };
        let x_ret = points1.special_point.getX();
        let points1 = Points { points: [p1, p2, p3], special_point: p_global2 };
        let p5 = points1.newPoint(38)
    }
    "#;
    assert_compile!(src);
}

#[test]
#[ignore]
fn test_higher_rank_trait_bounds() {
    let src = r#"
    struct Closure<F> {
        data: (u8, u16),
        func: F,
    }

    impl<F> Closure<F>
        where for<'a> F: Fn(&'a (u8, u16)) -> &'a u8,
    {
        fn call(&shrd cpu.mem self) -> &shrd cpu.mem u8 {
            (self.func)(&self.data)
        }
    }

    fn do_it(data: &shrd cpu.mem(u8, u16)) -[cpu.thread]-> &shrd cpu.mem u8 { &data.0 }

    fn mainf() -[cpu.thread]-> () {
        let clo = Closure { data: (0, 1), func: do_it };
        let res = clo.call()
    }
    "#;
    assert_compile!(src);
}
