use std::thread;

/*@
predicate tree_own(tree: *mut Tree, value: u64) =
    (*tree).value |-> value;

predicate tree_frac(tree: *mut Tree, value: u64, frac: real) =
    [frac](*tree).value |-> value;
@*/

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree
        //@ requires true;
        //@ ensures tree_own(result, v);
    {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64
        //@ requires tree_frac(tree, ?val, 1/2);
        //@ ensures tree_frac(tree, val, 1/2) &*& result == val + 1;
    {
        unsafe { (*tree).value + 1 }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64
        //@ requires tree_frac(tree, ?val, 1/2);
        //@ ensures tree_frac(tree, val, 1/2) &*& result == val + 2;
    {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64)
    //@ requires true;
    //@ ensures true;
{
    println!("{}", val);
}

fn main()
    //@ requires true;
    //@ ensures true;
{
    unsafe {
        let tree = Tree::make(22);
        //@ split_fraction tree_own(tree, 22) into tree_frac(tree, 22, 1/2), tree_frac(tree, 22, 1/2);

        let sum_join_handle = thread::spawn(move || {
            //@ open tree_frac(tree, 22, 1/2);
            let res = Tree::compute_sum_fibs(tree);
            //@ close tree_frac(tree, 22, 1/2);
            res
        });

        let product_join_handle = thread::spawn(move || {
            //@ open tree_frac(tree, 22, 1/2);
            let res = Tree::compute_product_fibs(tree);
            //@ close tree_frac(tree, 22, 1/2);
            res
        });

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
        
        //@ open tree_frac(tree, 22, 1/2);
        //@ open tree_frac(tree, 22, 1/2);
        //@ close tree_own(tree, 22);
        drop(Box::from_raw(tree));
    }
}