//@ predicate tree(t: *mut Tree; v: u64) = t as usize != 0 &*& struct_Tree_padding(t) &*& (*t).value |-> v;

use std::thread;

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree {
        //@ close tree(_0, v);
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        //@ open tree(tree, _v);
        unsafe { (*tree).value + 1 }
        //@ close tree(tree, _v);
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        //@ open tree(tree, _v);
        unsafe { (*tree).value + 2 }
        //@ close tree(tree, _v);
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()

{
    unsafe {
        let tree = Tree::make(22);
        

        

        
        let sum_join_handle = thread::spawn(move || {
            //@ open tree(tree, _v1);
            let res = Tree::compute_sum_fibs(tree);
            //@ close tree(tree, _v1);
            res
        });

        

        

        let product_join_handle = thread::spawn(move || {
            //@ open tree(tree, _v2);
            let res = Tree::compute_product_fibs(tree);
            //@ close tree(tree, _v2);
            res
        });

        
        let sum = sum_join_handle.join().unwrap();
        
        

        let product = product_join_handle.join().unwrap();
        
        

        print_u64(sum);
        print_u64(product);
    }
}