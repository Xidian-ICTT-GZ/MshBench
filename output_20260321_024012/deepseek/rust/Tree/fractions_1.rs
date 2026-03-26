use std::thread;

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        //@ req tree != 0;
        //@ req Tree_own(tree, _);
        //@ ens Tree_own(tree, _);
        unsafe { (*tree).value + 1 }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        //@ req tree != 0;
        //@ req Tree_own(tree, _);
        //@ ens Tree_own(tree, _);
        unsafe { (*tree).value + 2 }
    }
}

/*@
pred Tree_own(t: *mut Tree; v: u64) = struct_Tree_padding(t) &*& (*t).value |-> v;
@*/

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        //@ close Tree_own(tree, 22);
        
        let sum_join_handle = thread::spawn(move || {
            //@ open Tree_own(tree, _);
            let r = Tree::compute_sum_fibs(tree);
            //@ close Tree_own(tree, 22);
            r
        });

        let product_join_handle = thread::spawn(move || {
            //@ open Tree_own(tree, _);
            let r = Tree::compute_product_fibs(tree);
            //@ close Tree_own(tree, 22);
            r
        });

        let sum = sum_join_handle.join().unwrap();
        //@ open Tree_own(tree, _);
        
        let product = product_join_handle.join().unwrap();
        //@ open Tree_own(tree, _);
        //@ close Tree_own(tree, 22);
        //@ leak Tree_own(tree, _);
        let _ = Box::from_raw(tree);

        print_u64(sum);
        print_u64(product);
    }
}