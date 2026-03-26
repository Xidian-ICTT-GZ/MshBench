use std::thread;

/*@
pred Tree(t: *mut Tree; v: u64) {
    alloc_block(t, std::mem::size_of::<Tree>()) &*&
    struct_Tree_padding(t) &*&
    (*t).value |-> v;
}
@*/

struct Tree {
    value: u64,
}

impl Tree {
    //@ req true;
    //@ ens Tree(result, v);
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    //@ req Tree(tree, v);
    //@ ens Tree(tree, v) &*& result == v + 1;
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    //@ req Tree(tree, v);
    //@ ens Tree(tree, v) &*& result == v + 2;
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

//@ req true;
//@ ens true;
fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()
{
    unsafe {
        //@ close Tree::make_pre()();
        let tree = Tree::make(22);
        //@ open Tree::make_post()();
        //@ assume Tree(tree, 22);
        
        //@ close exists(22);
        let sum_join_handle = thread::spawn(move || {
            //@ open exists(v)();
            //@ open Tree(tree, v);
            let r = Tree::compute_sum_fibs(tree);
            //@ close Tree(tree, v);
            r
        });

        //@ close exists(22);
        let product_join_handle = thread::spawn(move || {
            //@ open exists(v)();
            //@ open Tree(tree, v);
            let r = Tree::compute_product_fibs(tree);
            //@ close Tree(tree, v);
            r
        });
        
        let sum = sum_join_handle.join().unwrap();
        //@ open Tree(_, _);
        //@ leak Tree(_, _);
        
        let product = product_join_handle.join().unwrap();
        //@ open Tree(_, _);
        //@ leak Tree(_, _);
        
        print_u64(sum);
        print_u64(product);
    }
}