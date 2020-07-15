extern crate descend;

use descend::ast::*;
use descend::dsl::*;
use descend::types::*;

#[test]
fn let_examples() {
    // let x: i32 = 5;
    //     desuggared:
    // let const x: un i32
    //   be 5
    //   in ()
    let l = r#let(
        "x",
        Ty::Data(DataTy::Un(CopyData::Scalar(ScalarData::I32))),
        Mutability::Const,
        lit(&5),
        tuple(vec![]),
    );
}
