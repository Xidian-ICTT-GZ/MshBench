use std::thread;

/*@

pred Tree_value(t: *mut Tree; v: u64) = (*t).value |-> v;

pred_ctor Tree_frac(t: *mut Tree, v: u64)(frac: real) = [frac]Tree_value(t, v);

@*/

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree
    //@ req true;
    //@ ens Tree_value(result, v);
    {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req [1/2]Tree_value(tree, ?v);
    //@ ens [1/2]Tree_value(tree, v) &*& result == v + 1;
    {
        unsafe { (*tree).value + 1 }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req [1/2]Tree_value(tree, ?v);
    //@ ens [1/2]Tree_value(tree, v) &*& result == v + 2;
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
        //@ open Tree_value(tree, 22);
        //@ close [1/2]Tree_value(tree, 22);
        //@ close [1/2]Tree_value(tree, 22);

        let sum = Tree::compute_sum_fibs(tree);

        let product = Tree::compute_product_fibs(tree);

        //@ open [1/2]Tree_value(tree, 22);
        //@ open [1/2]Tree_value(tree, 22);
        //@ close Tree_value(tree, 22);

        print_u64(sum);
        print_u64(product);

        //@ open Tree_value(tree, 22);
        let _ = Box::from_raw(tree);
    }
}