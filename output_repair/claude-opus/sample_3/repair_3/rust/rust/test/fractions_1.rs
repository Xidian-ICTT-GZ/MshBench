use std::thread;

/*@
predicate tree_own(tree: *mut Tree, value: u64) =
    (*tree).value |-> value;

predicate tree_frac(tree: *mut Tree, value: u64, frac: real) =
    [frac](*tree).value |-> value;

predicate thread_token(tree: *mut Tree, value: u64) =
    tree_frac(tree, value, 1r/2r);
@*/

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(tree_frac(tree, value, frac))]
    #[ensures(tree_frac(tree, value, frac))]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(tree_frac(tree, value, frac))]
    #[ensures(tree_frac(tree, value, frac))]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }

    #[ensures(tree_own(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

#[requires(tree_own(tree, 22u64))]
fn main_impl(tree: *mut Tree) {
    unsafe {
        let sum_join_handle = thread::spawn(move || {
            Tree::compute_sum_fibs(tree)
        });

        let product_join_handle = thread::spawn(move || {
            Tree::compute_product_fibs(tree)
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        main_impl(tree);
    }
}