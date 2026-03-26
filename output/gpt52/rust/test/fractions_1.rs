use std::thread;

struct Tree {
    value: u64,
}

/*@

predicate Tree_ptr(ptr: *mut Tree, v: u64) =
    ptr->value |-> v;

@*/

impl Tree {
    #[ensures(Tree_ptr(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(Tree_ptr(tree, ?v))]
    #[ensures(Tree_ptr(tree, v) &*& result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(Tree_ptr(tree, ?v))]
    #[ensures(Tree_ptr(tree, v) &*& result == v + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

#[requires(true)]
#[ensures(true)]
fn print_u64(val: u64) {
    println!("{}", val);
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let tree = Tree::make(22);

        //@ open Tree_ptr(tree, 22);

        let sum_join_handle = thread::spawn(move || {
            //@ close Tree_ptr(tree, 22);
            Tree::compute_sum_fibs(tree)
        });

        let product_join_handle = thread::spawn(move || {
            //@ close Tree_ptr(tree, 22);
            Tree::compute_product_fibs(tree)
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}