use std::thread;

#[pred_def TreePred(tree: *mut Tree, v: u64) = 
    emp &*& tree != 0 &*&
    *tree |-> ?t &*&
    t.value |-> v
]

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(result != 0 &*& TreePred(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(TreePred(tree, v))]
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

        let sum_join_handle = thread::spawn(move || {
            #[ghost]
            let _ = TreePred(tree, 22);
            Tree::compute_sum_fibs(tree)
        });

        let product_join_handle = thread::spawn(move || {
            #[ghost]
            let _ = TreePred(tree, 22);
            Tree::compute_product_fibs(tree)
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}