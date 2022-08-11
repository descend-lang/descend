#![cfg(test)]

extern crate descend;

macro_rules! assert_compile {
    ($src: expr) => {
        let res = descend::compile_src($src);
        if let Err(error) = res {
            eprintln!("{}\n{:#?}", $src, error);
            panic!("Unexpted error while typechecking");
        } else {
            println!("{}", res.unwrap())
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
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Eq {
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
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    impl Eq for i32 {
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
    trait Eq {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    impl Eq for Point {
    }
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
        let z = p2.x;
        ()
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_monomoprhisation() {
    let src = r#"
    trait Trait1 {}
    trait Trait2 {}
    trait Eq<X, Y> where X: Trait1 {
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
    impl<A, B, C> Eq<A, B> for Point<B, C> where A: Trait1 + Trait2, B: Trait2 {
        fn new<Z>(z: Z) -[cpu.thread]-> i32 {
            let mut a: A;
            let mut b: B;
            let p: Point<i32, i32> = Point<i32, i32> { x: 42, y: 43 };
            foo::<i32>(p, true); //TODO infer generic
            42
        }
    }
    impl Trait1 for i32 {}
    impl Trait2 for i32 {}
    impl Trait1 for f64 {}
    impl Trait2 for f64 {}

    fn foo<X, Z, T>(t: T, z: Z) -[cpu.thread] -> i32 where X: Trait1, T: Eq<X, X> {
        //T::new(z)
        T::new::<T, X, X, Z>(z) //TODO generics should be inferred
    }

    fn bar() -[cpu.thread]-> i32 {
        let p: Point<f64, i32> = Point<f64, i32> { x: 4.0, y: 42 };
        foo::<f64>(p, 42); //TODO infer generic
        let p2: Point<i32, f64> = Point<i32, f64> { x: 4, y: 42.0 };
        foo::<i32>(p2, 42.5); //TODO infer generic
        42
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_fun_calls() {
    let src = r#"
    trait Eq {
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
    impl<T> Eq for Point<T> where T: SomeOtherTrait {}
    fn fun_with_generics<T>(t: T) -[cpu.thread]-> () where T: Eq {
        let i1: i32 = (&shrd t).eq(&shrd t);
        let i2: i32 = T::eq(&shrd t, &shrd t);
        ()
    }
    fn fun_with_generics2<T>(t1: T, t2: T, t3: T, t4: T) -[cpu.thread]-> () where T: SomeOtherTrait  {
        let p: Point<T> = Point<T> { x: t1, y: t2 };
        fun_with_generics(p);

        let p2: Point<T> = Point<T> { x: t3, y: t4 };
        (&shrd p2).eq(&shrd p2);
        Point<T>::eq(&shrd p2, &shrd p2);
        // Point::eq(&shrd p2, &shrd p2); //TODO infer generic
        ()
    }
    fn bar() -[cpu.thread]-> () {
        fun_with_generics2(1, 2, 3, 4);
        ()
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Eq {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> i32 {
            1
        }
    }
    trait SomeOtherTrait {} //TODO why is this necassary to run the test sucessfully
    impl SomeOtherTrait for i32 {} //TODO why is this necassary to run the test sucessfully
    struct Point<T> {
        x: T,
        y: T
    }
    impl<T> Eq for Point<T> {} //here "T" has no constraints
    fn fun_with_generics<T>(t: T) -[cpu.thread]-> () where T: Eq {
        let i1: i32 = (&shrd t).eq(&shrd t);
        let i2: i32 = T::eq(&shrd t, &shrd t);
        ()
    }
    fn fun_with_generics2<T>(t1: T, t2: T, t3: T, t4: T) -[cpu.thread]-> () {
        let p: Point<T> = Point<T> { x: t1, y: t2 };
        fun_with_generics(p);

        let p2: Point<T> = Point<T> { x: t3, y: t4 };
        (&shrd p2).eq(&shrd p2);
        Point<T>::eq(&shrd p2, &shrd p2);
        // Point::eq(&shrd p2, &shrd p2); //TODO infer generic
        ()
    }
    fn bar() -[cpu.thread]-> () {
        fun_with_generics2(1, 2, 3, 4);
        ()
    }
    "#;
    assert_compile!(src); //This generates other code because "T" is not monomorphised
}

#[test]
#[ignore] //TODO why does this compile???
fn test_moved_struct_attribute() {
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
        let z2 = p.x; //Already moved
        ()
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
    trait Eq {
        //const important_const: f32;
        //const PANIC: () = panic!("compile-time panic");
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
        //const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    impl Eq for i32 {
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
    trait Eq {
        //const important_const: f32 = 4.2; // initialize with some value
        //const PANIC: () = panic!("compile-time panic");
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
        //const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            (*self).x == (*other).x && (*self).y == (*other).y
        }
    }
    impl Eq for i32 {
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
    // trait Eq {
    //     //const important_const: f32;
    //     //const PANIC: () = panic!("compile-time panic");
    //     fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    // }
    // impl Eq for Point {
    //     //const important_const = 4.2;
    //     fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
    //         (*self).x == (*other).x && (*self).y == (*other).y
    //     }
    // }
    // impl Eq for i32 {
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
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
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
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        fn eq2(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            true
        }
    }
    impl Eq for Point {
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
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
        fn eq2(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
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
    trait Eq<T> {
        fn eq(&shrd cpu.mem self, T) -[cpu.thread]-> bool;
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Eq<i32> {
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
        let x = Point<i32, i32> { x: 16, y: 4 }
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point<i32> { x: 16, y: 4 }
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point<i32, i32, i32> { x: 16, y: 4 }
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
    trait Eq<T> {}
    impl<T> Eq<T> for Point<i32, i32> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Eq<T> {}
    impl Eq<i32> for Point<i32, i32> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Eq<T> {}
    impl Eq for Point<i32, i32> {}
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Eq<T> {}
    impl Eq<> for Point<i32, i32> {}
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    trait Eq<T> {}
    impl Eq<i32, f32> for Point<i32, i32> {}
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
    trait Eq {}
    impl<T> Eq for Point<T, 42> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X: dty, n: nat> {
        x: X,
        y: [i32; n]
    }
    trait Eq {}
    impl<T, X: nat> Eq for Point<T, X> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X: ty, n: nat> {
        x: X,
        y: [i32; n]
    }
    trait Eq {}
    impl<T, X> Eq for Point<T, X> {}
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X: ty, n: nat> {
        x: X,
        y: [i32; n]
    }
    trait Eq {}
    impl<T: mem> Eq for Point<T, 42> {}
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_unfullfilled_constraints() {
    let src = r#"
    struct Struct1 { i: i32 }
    struct Struct2 { i: f32 }
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    struct Point<X, Y> where X: Eq, Y:Eq {
        x: X,
        y: Y
    }
    impl Eq for Struct1 {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    fn foo() -[cpu.thread]-> () {
        let x: Struct1 = Struct1 { i: 42 };
        let y: Struct1 = Struct1 { i: 43 };
        let p: Point<Struct1, Struct1> = Point<Struct1, Struct1> {x, y}
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Struct1 { i: i32 }
    struct Struct2 { i: i32 }
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    struct Point<X, Y> where X: Eq, Y:Eq {
        x: X,
        y: Y
    }
    impl Eq for Struct1 {
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
    trait Eq {
        fn foo(x: i32) -[cpu.thread]-> bool {
            false
        }
    }
    trait Ord: Eq {
        fn foo2(x: i32) -[cpu.thread]-> bool;
    }
    trait SOrd: Ord {
        fn foo3(x: i32) -[cpu.thread]-> bool;
    }
    struct Point<X, Y> where X: Eq, Y:Eq {
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
    // trait Eq {
    //     fn foo(x: i32) -[cpu.thread]-> bool {
    //         false
    //     }
    // }
    // trait Ord: Eq {
    //     fn foo2(x: i32) -[cpu.thread]-> bool {false}
    // }
    // trait SOrd: Ord {
    //     fn foo3(x: i32) -[cpu.thread]-> bool {false}
    // }
    // struct Point<X, Y> where X: Eq, Y:Eq {
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
    // trait Eq {
    //     fn foo(x: i32) -[cpu.thread]-> bool {
    //         false
    //     }
    // }
    // trait Ord: Eq {
    //     fn foo2(x: i32) -[cpu.thread]-> bool {false}
    // }
    // trait SOrd: Ord {
    //     fn foo3(x: i32) -[cpu.thread]-> bool {false}
    // }
    // struct Point<X, Y> where X: Eq, Y:Eq {
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
    impl<T> MyTrait for T where T: MyTrait {
        fn identity(t: T) -[cpu.thread]-> T {
            t
        }
    }
    struct Point<X> where X: MyTrait {
        x: X
    }
    fn foo() -[cpu.thread]-> () {
        let x: Point<i32> = Point<i32> { x: 42 }
    }
    "#;
    assert_err_compile!(src);
}

#[test]
#[ignore] //Dont work
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

#[test]
#[ignore] //TODO dont work
fn test_struct_with_lifetimes() {
    let src = r#"
    struct Test<'a> {
        x: &'a i32
    }
    impl<'a> Test<'a> {
        fn bar(&shrd cpu.mem self, i: i32) -[cpu.thread]-> i32 {
            i + self.x
        }
    }
    fn foo<'a>(t: Test<'a>) -[cpu.thread]-> i32 {
        t.x = 42;
        t.bar(15)
    }
    fn main() -[cpu.thread]-> () {
        let test: i32 = 1;
        let t = Test { x: &test };
        foo(t);
        ()
    }
    "
}

#[test]
#[ignore] //TODO dont work
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

    fn main() -[cpu.thread]-> () {
        let clo = Closure { data: (0, 1), func: do_it };
        let res = clo.call()
    }
    "#;
    assert_compile!(src);
}
