use std::thread;

/*@
predicate tree_own(tree: *mut Tree, value: u64) =
    (*tree).value |-> value;

predicate tree_frac(tree: *mut Tree, value: u64, frac: real) =
    [frac](*tree).value |-> value;

lemma split_tree_frac(tree: *mut Tree, value: u64, f1: real, f2: real)
    requires 0 < f1 && 0 < f2 && f1 + f2 <= 1.0 && tree_frac(tree, value, f1 + f2)
    ensures tree_frac(tree, value, f1) * tree_frac(tree, value, f2);

lemma merge_tree_frac(tree: *mut Tree, value: u64, f1: real, f2: real)
    requires 0 < f1 && 0 < f2 && f1 + f2 <= 1.0 && tree_frac(tree, value, f1) * tree_frac(tree, value, f2)
    ensures tree_frac(tree, value, f1 + f2);
@*/

struct Tree {
    value: u64,
}

impl Tree {
    #[verifier::requires(true)]
    #[verifier::ensures(tree_own(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[verifier::requires(tree_frac(tree, ?val, 1/2))]
    #[verifier::ensures(tree_frac(tree, val, 1/2) && result == val + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[verifier::requires(tree_frac(tree, ?val, 1/2))]
    #[verifier::ensures(tree_frac(tree, val, 1/2) && result == val + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

#[verifier::requires(true)]
#[verifier::ensures(true)]
fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        //@ split_fractional(tree_own(tree, 22), 1/2);

        let sum_join_handle = thread::spawn(move || {
            let res = Tree::compute_sum_fibs(tree);
            res
        });

        let product_join_handle = thread::spawn(move || {
            let res = Tree::compute_product_fibs(tree);
            res
        });

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);

        //@ merge_fractional(tree_frac(tree, 22, 1/2), tree_frac(tree, 22, 1/2));
        drop(Box::from_raw(tree));
    }
}