use std::thread;

#[pred]
pub predicate TreePred(tree: *mut Tree, v: u64) =
    tree != 0 &*&
    tree.value |-> v;

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(result != 0 &*& TreePred(result, v))]
    fn make(v: u64) -> *mut Tree {
        let b = Box::new(Tree { value: v });
        let p = Box::into_raw(b);
        open TreePred(p, v);
        close TreePred(p, v);
        p
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 1 &*& TreePred(tree, v))]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        open TreePred(tree, v);
        let res = unsafe { (*tree).value + 1 };
        close TreePred(tree, v);
        res
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 2 &*& TreePred(tree, v))]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        open TreePred(tree, v);
        let res = unsafe { (*tree).value + 2 };
        close TreePred(tree, v);
        res
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);

        // We split ownership to give both threads permission to read the tree.value:
        #[predicate]
        fn TreePred_split(tree: *mut Tree, v: u64) =
            tree.value |-> v;

        open TreePred(tree, 22);
        close TreePred(tree, 22);
        // In VeriFast, to allow sharing between threads, we can model fractional permissions.
        // Since TreePred models ownership of tree.value, and it is immutable, split into two fractions:
        // One for sum thread and one for product thread.

        #[ghost] // Ghost code to model permission splitting
        {
            // split TreePred into two halves:
            reveal TreePred(tree, 22);
            assert tree.value |-> 22;
            // Logically split the pointer predicate with fractional permission 1/2 each for two threads
            // VeriFast syntax for fractional permissions is like `tree.value |->[frac] 22`
            // We'll close predicates with half-fractional permissions for threads.

            // Close half permissions to thread closures (ghost)
            close [f32](tree.value |-> 22);
            close [f32](tree.value |-> 22);
        }

        // Spawn threads giving each half permission of the predicate
        let sum_join_handle = thread::spawn(move || {
            #[requires(tree.value |->[f32] 22)]
            #[ensures(tree.value |->[f32] 22)]
            {
                Tree::compute_sum_fibs(tree)
            }
        });

        let product_join_handle = thread::spawn(move || {
            #[requires(tree.value |->[f32] 22)]
            #[ensures(tree.value |->[f32] 22)]
            {
                Tree::compute_product_fibs(tree)
            }
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);

        // Recombine permissions and free the tree
        #[ghost] {
            // Recombine fractional permissions for full ownership
            open [f32](tree.value |-> 22);
            open [f32](tree.value |-> 22);
            close TreePred(tree, 22);
        }
        unsafe { Box::from_raw(tree); } // free memory
    }
}