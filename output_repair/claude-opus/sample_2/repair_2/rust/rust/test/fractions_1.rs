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
    #[ensures(result != std::ptr::null_mut())]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(tree_frac(tree, ?v, 1/2))]
    #[ensures(result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(tree_frac(tree, ?v, 1/2))]
    #[ensures(result == v + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);

        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));

        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}