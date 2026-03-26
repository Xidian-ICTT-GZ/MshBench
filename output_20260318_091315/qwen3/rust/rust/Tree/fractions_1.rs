use std::thread;

predicate tree(t: *mut Tree, v: u64) = (*t).value |-> v;

impl Tree {
    #[requires(true)]
    #[ensures(tree(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(tree(tree, v))]
    #[ensures(tree(tree, v) && result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(tree(tree, v))]
    #[ensures(tree(tree, v) && result == v + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let tree = Tree::make(22);
        
        let sum_join_handle = thread::spawn(move || {
            let s = Tree::compute_sum_fibs(tree);
            s
        });

        let product_join_handle = thread::spawn(move || {
            let p = Tree::compute_product_fibs(tree);
            p
        });

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}