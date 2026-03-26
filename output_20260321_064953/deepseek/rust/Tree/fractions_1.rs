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
        //@ ens true;
        unsafe { (*tree).value + 1 }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        //@ req tree != 0;
        //@ ens true;
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    //@ req true;
    //@ ens true;
    println!("{}", val);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        //@ close Tree_own(tree, 22);
        //@ let tree2 = tree;

        let sum_join_handle = thread::spawn(move || {
            //@ open Tree_own(tree, _);
            Tree::compute_sum_fibs(tree)
        });

        let product_join_handle = thread::spawn(move || {
            //@ open Tree_own(tree2, _);
            Tree::compute_product_fibs(tree2)
        });

        let sum = sum_join_handle.join().unwrap();
        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}

/*@
pred Tree_own(tree: *mut Tree; v: u64) = struct_Tree_padding(tree) &*& (*tree).value |-> v;
@*/