use std::thread;

#[pred_def TreePred(tree: *mut Tree, v: u64) = 
    tree != 0 &*&
    tree->value |-> v
]

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(result != 0 &*& TreePred(result, v))]
    fn make(v: u64) -> *mut Tree {
        let b = Box::new(Tree { value: v });
        let p = Box::into_raw(b);
        p
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            tree->value |-> v;
            let r = (*tree).value + 1;
            r
        }
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            tree->value |-> v;
            let r = (*tree).value + 2;
            r
        }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        open TreePred(tree, 22);
        #[ghost] let tree_ownership = TreePred(tree, 22);

        // Transfer ownership to the spawned threads by splitting into two fractions
        #[predicate]
        predicate TreePredHalf(tree: *mut Tree) = tree->value |-> _; 

        // We split ownership
        split_tree_pred(tree, 22);

        let sum_join_handle = {
            let tree_sum = tree; // take full ownership for thread
            thread::spawn(move || {
                open TreePredHalf(tree_sum);
                let res = Tree::compute_sum_fibs(tree_sum);
                close TreePredHalf(tree_sum);
                res
            })
        };

        let product_join_handle = {
            let tree_product = tree;
            thread::spawn(move || {
                open TreePredHalf(tree_product);
                let res = Tree::compute_product_fibs(tree_product);
                close TreePredHalf(tree_product);
                res
            })
        };

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        // Rejoin ownership fractions
        join_tree_pred(tree, 22);

        print_u64(sum);
        print_u64(product);
    }

}

// Lemmas to split and join ownership fractions of TreePred
#[lemma]
fn split_tree_pred(tree: *mut Tree, v: u64)
    requires TreePred(tree, v);
    ensures TreePredHalf(tree) &*& TreePredHalf(tree);
{
    open TreePred(tree, v);
    close TreePredHalf(tree);
    close TreePredHalf(tree);
}

#[lemma]
fn join_tree_pred(tree: *mut Tree, v: u64)
    requires TreePredHalf(tree) &*& TreePredHalf(tree);
    ensures TreePred(tree, v);
{
    open TreePredHalf(tree);
    open TreePredHalf(tree);
    close TreePred(tree, v);
}