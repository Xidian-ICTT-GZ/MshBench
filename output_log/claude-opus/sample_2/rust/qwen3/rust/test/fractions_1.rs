use std::thread;

#[pred]
pub predicate TreePred(tree: *mut Tree, v: u64) = 
    tree != 0 &*&
    tree->value |-> v;

struct Tree {
    value: u64,
}

impl Tree {
    #[requires(true)]
    #[ensures(result != 0 &*& TreePred(result, v))]
    fn make(v: u64) -> *mut Tree {
        let tree = Box::new(Tree { value: v });
        let tree_ptr = Box::into_raw(tree);
        tree_ptr
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 1 &*& TreePred(tree, v))]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            (*tree).value + 1
        }
    }

    #[requires(TreePred(tree, v))]
    #[ensures(result == v + 2 &*& TreePred(tree, v))]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            (*tree).value + 2
        }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);

        #[predicate]
        ghost fn thread_fun(tree: *mut Tree, v: u64);

        #[requires(TreePred(tree, 22))]
        #[ensures(true)]
        let sum_join_handle = thread::spawn(move || {
            Tree::compute_sum_fibs(tree)
        });

        #[requires(TreePred(tree, 22))]
        #[ensures(true)]
        let product_join_handle = thread::spawn(move || {
            Tree::compute_product_fibs(tree)
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}