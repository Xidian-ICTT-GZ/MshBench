use std::thread;

/*@
predicate tree_own(tree: *mut Tree, value: u64) =
    (*tree).value |-> value;

predicate tree_frac(tree: *mut Tree, value: u64, frac: real) =
    [frac](*tree).value |-> value;
@*/

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(tree_own(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(tree_frac(tree, ?val, 1r/2r))]
    #[ensures(tree_frac(tree, val, 1r/2r) &*& result == val + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(tree_frac(tree, ?val, 1r/2r))]
    #[ensures(tree_frac(tree, val, 1r/2r) &*& result == val + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

#[requires(true)]
#[ensures(true)]
fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        //@ split_frac(tree_own(tree, 22), tree_frac(tree, 22, 1r/2r), tree_frac(tree, 22, 1r/2r));

        let sum_join_handle = thread::spawn(move || -> u64 {
            //@ open tree_frac(tree, 22, 1r/2r);
            let r = Tree::compute_sum_fibs(tree);
            //@ close tree_frac(tree, 22, 1r/2r);
            r
        });

        let product_join_handle = thread::spawn(move || -> u64 {
            //@ open tree_frac(tree, 22, 1r/2r);
            let r = Tree::compute_product_fibs(tree);
            //@ close tree_frac(tree, 22, 1r/2r);
            r
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}