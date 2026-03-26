use std::thread;

struct Tree {
    value: u64,
}

/*@

pred tree_pred(t: pointer) = t->value |-> _;

@*/
impl Tree {
    /*@ requires true; ensures result: pointer &*& tree_pred(result); @*/
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    /*@ requires tree_pred(tree); ensures true; @*/
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    /*@ requires tree_pred(tree); ensures true; @*/
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()

/*@ requires true;
    ensures true;
@*/
{
    unsafe {
        let tree = Tree::make(22);
        //@ open tree_pred(tree);
        

        

        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));
        //@ close tree_pred(tree);
        
        

        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        
        let sum = sum_join_handle.join().unwrap();
        

        let product = product_join_handle.join().unwrap();
        

        print_u64(sum);
        print_u64(product);
    }
}