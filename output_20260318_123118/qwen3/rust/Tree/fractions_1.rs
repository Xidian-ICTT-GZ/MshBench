use std::thread;

predicate tree(t: *mut Tree) = (*t).value |-> _;

impl Tree {
    #[requires(true)]
    #[ensures(tree(result))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(tree(tree))]
    #[ensures(tree(tree) && result == (*tree).value + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(tree(tree))]
    #[ensures(tree(tree) && result == (*tree).value + 2)]
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
        
        let sum_join_handle = thread::spawn(move || {
            //@ open tree(tree);
            let res = Tree::compute_sum_fibs(tree);
            //@ close tree(tree);
            res
        });

        let product_join_handle = thread::spawn(move || {
            //@ open tree(tree);
            let res = Tree::compute_product_fibs(tree);
            //@ close tree(tree);
            res
        });

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}