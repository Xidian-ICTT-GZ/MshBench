use std::thread;

/*@ pred tree(t: *mut Tree, v: u64) = alloc_block_tree(t, 1) &*& struct_Tree_padding((*t).value |-> v); @*/

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
        unsafe { (*tree).value + 1 }
    }

    //@ req tree(tree, ?v);
    //@ ens tree(tree, v) &*& result == v + 2;
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

//@ req true;
//@ ens true;
fn print_u64(val: u64) {
    println!("{}", val);
}

//@ req true;
//@ ens true;
fn main()

{
    unsafe {
        let tree = Tree::make(22);
        

        

        
        let sum_join_handle = thread::spawn(move || {
            //@ open tree(tree, _);
            Tree::compute_sum_fibs(tree)
        });

        

        

        let product_join_handle = thread::spawn(move || {
            //@ open tree(tree, _);
            Tree::compute_product_fibs(tree)
        });

        
        let sum = sum_join_handle.join().unwrap();
        
        

        let product = product_join_handle.join().unwrap();
        
        

        print_u64(sum);
        print_u64(product);
    }
}