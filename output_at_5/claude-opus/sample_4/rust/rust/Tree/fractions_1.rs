use std::thread;

struct Tree {
    value: u64,
}

/*@
pred tree_pred(t: *mut Tree) = t->value |-> _;
@*/
impl Tree {
    /*@ requires true; ensures tree_pred(result); @*/
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    /*@ requires tree_pred(tree); ensures tree_pred(tree); @*/
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    /*@ requires tree_pred(tree); ensures tree_pred(tree); @*/
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

// Wrapper type for verifying Send with VeriFast thread spawn
struct ThreadSafeTree(*mut Tree);

/*@
predicate thread_safe_tree_pred(tst: ThreadSafeTree) = tree_pred(tst.0);

ghost impl Send for ThreadSafeTree;
@*/

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()
/*@ requires true; ensures true; @*/
{
    unsafe {
        let tree = Tree::make(22);

        //@ open tree_pred(tree);
        // create two thread-safe wrappers pointing to same tree pointer
        let ts_tree1 = ThreadSafeTree(tree);
        let ts_tree2 = ThreadSafeTree(tree);

        // Spawn thread for sum computation
        let sum_join_handle = thread::spawn(move || {
            //@ open thread_safe_tree_pred(ts_tree1);
            let res = Tree::compute_sum_fibs(ts_tree1.0);
            //@ close thread_safe_tree_pred(ts_tree1);
            res
        });

        // Spawn thread for product computation
        let product_join_handle = thread::spawn(move || {
            //@ open thread_safe_tree_pred(ts_tree2);
            let res = Tree::compute_product_fibs(ts_tree2.0);
            //@ close thread_safe_tree_pred(ts_tree2);
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