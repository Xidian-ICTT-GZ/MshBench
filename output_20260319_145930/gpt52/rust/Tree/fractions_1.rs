use std::thread;

/*@

pred tree(tree: *mut Tree; v: u64) =
    tree != 0 &*&
    alloc_block_Tree(tree) &*&
    (*tree).value |-> v;

@*/

struct Tree {
    value: u64,
}

impl Tree {
    //@ req true;
    //@ ens tree(result, v);
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    //@ req tree(tree, ?v);
    //@ ens tree(tree, v) &*& result == v + 1;
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            //@ open tree(tree, ?v);
            let res = (*tree).value + 1;
            //@ close tree(tree, v);
            res
        }
    }

    //@ req tree(tree, ?v);
    //@ ens tree(tree, v) &*& result == v + 2;
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe {
            //@ open tree(tree, ?v);
            let res = (*tree).value + 2;
            //@ close tree(tree, v);
            res
        }
    }
}

//@ req true;
//@ ens true;
fn print_u64(val: u64) {
    //@ assume_correct
    println!("{}", val);
}

//@ req true;
//@ ens true;
fn main()

{
    unsafe {
        let tree = Tree::make(22);
        //@ open tree(tree, 22);

        //@ close tree(tree, 22);
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