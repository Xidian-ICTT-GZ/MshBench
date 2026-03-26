use std::thread;

struct Tree {
    value: u64,
}

impl Tree {
    #[predicate]
    fn tree_own(self: *mut Tree, v: u64) -> bool {
        points_to(self, 1, Tree { value: v })
    }

    #[predicate]
    fn tree_frac(self: *mut Tree, v: u64, f: rational) -> bool {
        points_to(self, f, Tree { value: v })
    }

    #[requires(tree_own(@tree, v))]
    #[ensures(tree_own(@result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(tree_frac(@tree, v, 1/2))]
    #[ensures(tree_frac(@tree, v, 1/2))]
    #[ensures(result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(tree_frac(@tree, v, 1/2))]
    #[ensures(tree_frac(@tree, v, 1/2))]
    #[ensures(result == v + 2)]
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
        proof_assert! { Tree::tree_own(@tree, 22) };

        let tree_frac1 = Tree::tree_frac(@tree, 22, 1/2);
        let tree_frac2 = Tree::tree_frac(@tree, 22, 1/2);
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