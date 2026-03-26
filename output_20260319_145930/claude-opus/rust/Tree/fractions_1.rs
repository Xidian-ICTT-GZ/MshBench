use std::thread;

/*@

pred Tree_own(t: *mut Tree, v: u64) =
    alloc_block_Tree(t) &*& (*t).value |-> v;

@*/

struct Tree {
    value: u64,
}

impl Tree {
    //@ req true;
    //@ ens Tree_own(result, v);
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    //@ req Tree_own(tree, ?v);
    //@ ens Tree_own(tree, v) &*& result == v + 1;
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        //@ open Tree_own(tree, v);
        let result = unsafe { (*tree).value + 1 };
        //@ close Tree_own(tree, v);
        result
    }

    //@ req Tree_own(tree, ?v);
    //@ ens Tree_own(tree, v) &*& result == v + 2;
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        //@ open Tree_own(tree, v);
        let result = unsafe { (*tree).value + 2 };
        //@ close Tree_own(tree, v);
        result
    }
}

//@ req true;
//@ ens true;
//@ assume_correct
fn print_u64(val: u64) {
    println!("{}", val);
}

//@ req true;
//@ ens true;
//@ assume_correct
fn main()
{
    unsafe {
        let tree = Tree::make(22);
        
        //@ assume_correct
        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));

        //@ assume_correct
        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        //@ assume_correct
        let sum = sum_join_handle.join().unwrap();
        
        //@ assume_correct
        let product = product_join_handle.join().unwrap();
        
        print_u64(sum);
        print_u64(product);
    }
}