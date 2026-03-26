use std::thread;

struct Tree {
    value: u64,
}

//@ pred tree_ptr(t: *mut Tree) = pointer(t, _) &*& malloc_block<Tree>(t);

impl Tree {
    //@ requires true;
    //@ ensures tree_ptr(result);
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    //@ requires tree_ptr(tree);
    //@ ensures true;
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    //@ requires tree_ptr(tree);
    //@ ensures true;
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()

{
    unsafe {
        let tree = Tree::make(22);
        //@ open tree_ptr(tree);

        

        

        
        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));

        

        

        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        
        let sum = sum_join_handle.join().unwrap();
        
        

        let product = product_join_handle.join().unwrap();
        
        

        print_u64(sum);
        print_u64(product);
        //@ close tree_ptr(tree);
        let _ = Box::from_raw(tree);
    }
}