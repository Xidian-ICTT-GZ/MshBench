use std::thread;

#[predicate]
pub fn TreePred(tree: *mut Tree, v: u64) = 
    tree != std::ptr::null_mut() &*&
    tree->value |-> v;

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(result != std::ptr::null_mut() && TreePred(result, v))]
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
        #[ghost] let tree_perm = TreePred(tree, 22);

        let sum_join_handle = thread::spawn(move || {
            open TreePred(tree, 22);
            let res = Tree::compute_sum_fibs(tree);
            close TreePred(tree, 22);
            res
        });

        let product_join_handle = thread::spawn(move || {
            open TreePred(tree, 22);
            let res = Tree::compute_product_fibs(tree);
            close TreePred(tree, 22);
            res
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);

        close TreePred(tree, 22);
        // Deallocate tree, now with full ownership back
        Box::from_raw(tree);
    }
}