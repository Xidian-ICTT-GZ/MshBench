use std::thread;

/*@

pred Tree_own(t: *mut Tree; v: u64) = (*t).value |-> v;

@*/

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree
    //@ req true;
    //@ ens Tree_own(result; v);
    {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req Tree_own(tree; ?v);
    //@ ens Tree_own(tree; v);
    {
        unsafe { (*tree).value + 1 }
    }

    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req Tree_own(tree; ?v);
    //@ ens Tree_own(tree; v);
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
        
        let sum = Tree::compute_sum_fibs(tree);
        
        let product = Tree::compute_product_fibs(tree);
        
        print_u64(sum);
        print_u64(product);
    }
}