use std::thread;

struct Tree {
    value: u64,
}

/*@
pred tree_pred(t: *mut Tree) = t->value |-> _;
@*/
impl Tree {
    /*@ requires true; ensures result: tree_pred(result); @*/
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    /*@ requires tree_pred(tree); ensures tree_pred(tree); @*/
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            (*tree).value + 1
        }
    }

    /*@ requires tree_pred(tree); ensures tree_pred(tree); @*/
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            (*tree).value + 2
        }
    }
}

// Helper wrapper for thread safety
struct ThreadSafeTree(*mut Tree);

// Implement Send for ThreadSafeTree ghostly for VeriFast verification
/*@ ghost impl Send for ThreadSafeTree; @*/

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()
/*@ requires true; ensures true; @*/
{
    unsafe {
        let tree = Tree::make(22);
        //@ open tree_pred(tree);

        let ts_tree = ThreadSafeTree(tree);

        // Spawn thread for sum
        let sum_join_handle = thread::spawn(move || {
            // Re-establish predicate inside thread
            //@ open tree_pred(ts_tree.0);
            let res = Tree::compute_sum_fibs(ts_tree.0);
            //@ close tree_pred(ts_tree.0);
            res
        });

        // Spawn thread for product
        let ts_tree2 = ThreadSafeTree(tree);
        let product_join_handle = thread::spawn(move || {
            //@ open tree_pred(ts_tree2.0);
            let res = Tree::compute_product_fibs(ts_tree2.0);
            //@ close tree_pred(ts_tree2.0);
            res
        });

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        //@ close tree_pred(tree);
        print_u64(sum);
        print_u64(product);
    }
}

// verifast_options{--opaque-pointer-predicates}