use insta;
use minnie::ast::parse_expr;

///! Tests the parse tree of small expressions that are best tested individually.
///! These tests are verified with snapshots in the snapshots/ directory.
///! See instructions in `tests/README.md` for updating snapshot results.

macro_rules! parse_expr {
    ($name:ident, $text:expr) => {
        #[test]
        fn $name() {
            insta::assert_ron_snapshot!(parse_expr($text).map(|b| b.ast.item));
        }
    };
}

parse_expr! { comparison_eq_precedence,
    "1 + 2 == 2 + 1"
}

parse_expr! { comparison_eq_precedence_2,
    "-1 == - 2"
}

parse_expr! { comparison_type_mismatch,
    "5 == false"
}

parse_expr! { math_type_mismatch,
    "1 + true"
}

parse_expr! { math_precedence,
    "1 + 2 * -3 < 0"
}

parse_expr! { call_0, "print_num(1);" }
parse_expr! { call_1, "({print_num})(1);" }
