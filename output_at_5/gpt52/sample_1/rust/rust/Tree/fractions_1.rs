use std::thread;

//@ pred Tree_ptr(p: *mut Tree) = p != 0 &*& (*p).value |-> ?v;

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree
    //@ req true;
    //@ ens Tree_ptr(result);
    {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req Tree_ptr(tree);
    //@ ens Tree_ptr(tree);
    {
        unsafe { (*tree).value + 1 }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req Tree_ptr(tree);
    //@ ens Tree_ptr(tree);
    {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64)
//@ req true;
//@ ens true;
{
    println!("{}", val);
}

fn main()
//@ req true;
//@ ens true;

{
    unsafe {
        let tree = Tree::make(22);
        //@ open Tree_ptr(tree);

        

        

        
        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));

        

        

        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        
        let sum = sum_join_handle.join().unwrap();
        
        

        let product = product_join_handle.join().unwrap();
        
        

        print_u64(sum);
        print_u64(product);
    }
}