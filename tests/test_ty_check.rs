#![cfg(test)]

extern crate descend;

macro_rules! assert_compile {
    ($src: expr) => {
        let res = descend::compile($src);
        if let Err(error) = res {
            eprintln!("{}\n{:#?}", $src, error);
            panic!("Unexpted error while typechecking");
        }
    };
}

macro_rules! assert_err_compile {
    ($src: expr) => {
        let res = descend::compile($src);
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
        const magic_number: i32 = 42;
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
            self.x == other.x && self.y == other.y
        }
    }
    impl Eq for i32 {
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            self == other
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
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    impl Point {
        fn foo(self) -[cpu.thread]-> Point {
            self
        }
    }
    fn bar() -[cpu.thread]-> i32 {
        let x = 3;
        let p = Point { x, y: 42 };
        let z = p.x;
        let p2 = p.foo();
        let x2 = p.foo().x;
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    impl Point {
        fn foo(self) -[cpu.thread]-> Point {
            self
        }
    }
    fn bar() -[cpu.thread]-> i32 {
        let x = 3;
        let p = Point { x, y: 42 };
        let z = p.x;
        let z2 = p.x; //Already moved
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Eq {
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool {
            false
        }
    }
    impl Point {
        fn foo(self) -[cpu.thread]-> Point {
            self
        }
    }
    fn bar() -[cpu.thread]-> i32 {
        let x = 3;
        let p = Point { x, y: 42 };
        let p2 = (&shrd p).eq(&shrd p);
        let p3 = eq(&shrd p, &shrd p)
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_associated_const() {
    let src = r#"
    struct Point {
        x: i32,
        y: i32
    }
    trait Eq {
        const important_const: f32;
        const PANIC: () = panic!("compile-time panic");
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
        const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            self.x == other.x && self.y == other.y
        }
    }
    impl Eq for i32 {
        const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            let _ = PANIC;
            self == other
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
        const important_const: f32 = 4.2; // initialize with some value
        const PANIC: () = panic!("compile-time panic");
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
        const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            self.x == other.x && self.y == other.y
        }
    }
    impl Eq for i32 {
        const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            let _ = PANIC;
            self == other
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
        const important_const: f32;
        const PANIC: () = panic!("compile-time panic");
        fn eq(&shrd cpu.mem self, &shrd cpu.mem Self) -[cpu.thread]-> bool;
    }
    impl Eq for Point {
        const important_const = 4.2;
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            self.x == other.x && self.y == other.y
        }
    }
    impl Eq for i32 {
        //No definion of "important_const"
        fn eq(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            let _ = PANIC;
            self == other
        }
    }
    "#;
    assert_err_compile!(src);
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
            self.x == other.x && self.y == other.y
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
            self.x == other.x && self.y == other.y
        }
        fn eq2(&shrd cpu.mem self, other: &shrd cpu.mem Self) -[cpu.thread]-> bool {
            self.x == other.x && self.y == other.y
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
            self.x == other.x && self.y == other.y
        }
    }
    "#;
    assert_compile!(src);
}

#[test]
fn test_multiple_gl_fun_with_same_name() {
    let src = r#"
    fn foo() -[cpu.thread]-> () {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo() -[cpu.thread]-> () {
        42
    }
    fn foo() -[cpu.thread]-> () {
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
fn test_multiple_structs_and_traits_with_same_name() {
    let src = r#"
    struct Test {}
    "#;
    assert_compile!(src);
    let src = r#"
    trait Test {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test {}
    trait Test {}
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
    fn foo(x: i32, y: f32) -[cpu.thread]-> () {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    fn foo(x: i32, x: f32) -[cpu.thread]-> () {
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
            42
        }
        fn foo2(x: i32, y: f32) -[cpu.thread]-> ();
    }
    "#;
    assert_compile!(src);

    let src = r#"
    trait Test {
        fn foo(x: i32, y: f32) -[cpu.thread]-> () {
            42
        }
        fn foo(x: i32, y: f32) -[cpu.thread]-> ();
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_multiple_generics_with_same_name() {
    let src = r#"
    struct Test<X: Nat, Y: Nat> { x: X, y: Y }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Test<X: Nat, X: Nat> { x: X, y: Y }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_ambious_generic_struct_name() {
    let src = r#"
    struct T {}
    fn foo<X>(x: T, y: X) -[cpu.thread]-> () {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct T {}
    fn foo<T>(x: T, y: T) -[cpu.thread]-> () {
        42
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_invalid_type_in_fn() {
    let src = r#"
    struct T {}
    fn foo(x: T) -[cpu.thread]-> () {
        42
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct T {}
    fn foo(x: Ta) -[cpu.thread]-> () {
        42
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct T {}
    fn foo(x: Ty) -[cpu.thread]-> () {
        42
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct T {}
    fn foo(x: X) -[cpu.thread]-> () {
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
        let x = Point<i32, i32>
    }
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point<i32>
    }
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X, Y> {
        x: X,
        y: Y
    }
    fn foo() -[cpu.thread]-> () {
        let x = Point<i32, i32, i32>
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
    struct Point<X: Ty, Y: Nat> {
        x: X,
        y: Y
    }
    trait Eq {}
    impl<T> Eq for Point<T, 42> {}
    "#;
    assert_compile!(src);

    let src = r#"
    struct Point<X: Ty, Y: Nat> {
        x: X,
        y: Y
    }
    trait Eq {}
    impl<T> Eq for Point<T, 42.3> {}
    "#;
    assert_err_compile!(src);

    let src = r#"
    struct Point<X: Ty, Y: Nat> {
        x: X,
        y: Y
    }
    trait Eq {}
    impl<T: mem> Eq for Point<T, 42.3> {}
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
        let p: Point<Struct1, Struct1> = Point {x, y}
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
        let p: Point<Struct1, Struct2> = Point {x, y}
    }
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_unfullfilled_constraints2() {
    let src = r#"
    trait Eq {
        fn foo(x: i32) -[cpu.thread]-> bool {
            42
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

    let src = r#"
    trait Eq {
        fn foo(x: i32) -[cpu.thread]-> bool {
            false
        }
    }
    trait Ord: Eq {
        fn foo2(x: i32) -[cpu.thread]-> bool {false}
    }
    trait SOrd: Ord {
        fn foo3(x: i32) -[cpu.thread]-> bool {false}
    }
    struct Point<X, Y> where X: Eq, Y:Eq {
        x: X,
        y: Y
    }
    struct T<X> where X: Ord {} 
    struct Point2<Y> where Y: SOrd {
        p: Point<T<Y>, Y>
    }
    impl SOrd for T<X> where X: SOrd {}
    "#;
    assert_compile!(src);

    let src = r#"
    trait Eq {
        fn foo(x: i32) -[cpu.thread]-> bool {
            false
        }
    }
    trait Ord: Eq {
        fn foo2(x: i32) -[cpu.thread]-> bool {false}
    }
    trait SOrd: Ord {
        fn foo3(x: i32) -[cpu.thread]-> bool {false}
    }
    struct Point<X, Y> where X: Eq, Y:Eq {
        x: X,
        y: Y
    }
    struct T<X> where X: Ord {} 
    struct Point2<Y> where Y: Ord {
        p: Point<T<Y>, Y>
    }
    impl SOrd for T<X> where X: SOrd {}
    "#;
    assert_err_compile!(src);
}

#[test]
fn test_cylic_constraints() {
    let src = r#"
    impl<T> MyTrait for T where T: MyTrait {
        fn identity(T) -> T {
            T
        }
    }
    struct Point<X> where X: MyTrait {
        x: X
    }
    fn foo() -[cpu.thread]-> () {
        let x: Point<i32> = Point<i32> { x: 42 }
    }
    "#;
    assert_compile!(src);
}

#[test]
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
