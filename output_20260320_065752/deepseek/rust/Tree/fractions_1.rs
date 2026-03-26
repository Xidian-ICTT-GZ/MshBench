use std::thread;

/*@
pred Tree(tree: *mut Tree; value: u64) =
    alloc_block(tree, std::mem::size_of::<Tree>()) &*&
    struct_Tree_padding(tree) &*&
    (*tree).value |-> value;
@*/

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree {
        //@ req true;
        //@ ens Tree(result, v);
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        //@ req Tree(tree, ?value);
        //@ ens Tree(tree, value) &*& result == value + 1;
        unsafe { (*tree).value + 1 }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        //@ req Tree(tree, ?value);
        //@ ens Tree(tree, value) &*& result == value + 2;
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    //@ req true;
    //@ ens true;
    println!("{}", val);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = Tree::make(22);
        //@ close Tree(tree, 22);
        
        let sum_join_handle = thread::spawn(move || {
            //@ open Tree(tree, 22);
            Tree::compute_sum_fibs(tree)
        });

        let product_join_handle = thread::spawn(move || {
            //@ open Tree(tree, 22);
            Tree::compute_product_fibs(tree)
        });

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}