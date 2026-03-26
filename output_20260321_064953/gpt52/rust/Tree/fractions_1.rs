use std::thread;

struct Tree {
    value: u64,
}

/*@

pred tree(tree: *mut Tree; v: u64) =
    tree != std::ptr::null_mut() &*& (*tree).value |-> v;

@*/

impl Tree {
    fn make(v: u64) -> *mut Tree
    //@ req true;
    //@ ens tree(result, v);
    {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?v);
    //@ ens tree(tree, v) &*& result == v + 1;
    {
        unsafe {
            //@ open tree(tree, v);
            let res = (*tree).value + 1;
            //@ close tree(tree, v);
            res
        }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?v);
    //@ ens tree(tree, v) &*& result == v + 2;
    {
        unsafe {
            //@ open tree(tree, v);
            let res = (*tree).value + 2;
            //@ close tree(tree, v);
            res
        }
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
        //@ open tree(tree, 22);
        //@ close tree(tree, 22);
        

        

        
        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));

        

        

        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        
        let sum = sum_join_handle.join().unwrap();
        
        

        let product = product_join_handle.join().unwrap();
        
        

        print_u64(sum);
        print_u64(product);
    }
}