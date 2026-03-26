use std::thread;

struct Tree {
    value: u64,
}

impl Tree {
    #[predicate]
    fn tree_own(self: *mut Tree, v: u64) -> bool {
        pearlite! { self != 0 && (*self).value == v }
    }

    #[requires(self != 0)]
    #[ensures(result != 0 && Tree::tree_own(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(Tree::tree_own(tree, ?v))]
    #[ensures(Tree::tree_own(tree, v) && result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(Tree::tree_own(tree, ?v))]
    #[ensures(Tree::tree_own(tree, v) && result == v + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

#[predicate]
fn tree_full(tree: *mut Tree, v: u64) -> bool {
    Tree::tree_own(tree, v)
}

#[predicate]
fn tree_half(tree: *mut Tree, v: u64) -> bool {
    Tree::tree_own(tree, v)
}

#[predicate]
fn join_token() -> bool { true }

#[requires(tree_full(tree, v))]
#[ensures(tree_half(tree, v) && tree_half(tree, v) && join_token())]
fn split_tree(tree: *mut Tree, v: u64) {
    pearlite! { }
}

#[requires(tree_half(tree, v) && tree_half(tree, v) && join_token())]
#[ensures(tree_full(tree, v))]
fn merge_tree(tree: *mut Tree, v: u64) {
    pearlite! { }
}

#[requires(tree_half(tree, v))]
#[ensures(tree_half(tree, v))]
fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        let v = 22;
        
        proof_assert! { tree_full(tree, v) };
        split_tree(tree, v);
        
        let tree1 = tree;
        let tree2 = tree;
        
        let sum_join_handle = thread::spawn(move || {
            proof_assert! { tree_half(tree1, v) };
            let res = Tree::compute_sum_fibs(tree1);
            proof_assert! { tree_half(tree1, v) };
            res
        });

        let product_join_handle = thread::spawn(move || {
            proof_assert! { tree_half(tree2, v) };
            let res = Tree::compute_product_fibs(tree2);
            proof_assert! { tree_half(tree2, v) };
            res
        });
        
        let sum = sum_join_handle.join().unwrap();
        proof_assert! { tree_half(tree, v) };
        
        let product = product_join_handle.join().unwrap();
        proof_assert! { tree_half(tree, v) };
        
        merge_tree(tree, v);
        
        print_u64(sum);
        print_u64(product);
        
        drop(Box::from_raw(tree));
    }
}