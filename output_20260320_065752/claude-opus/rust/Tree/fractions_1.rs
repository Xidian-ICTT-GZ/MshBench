use std::thread;

/*@ pred tree(struct Tree *t;) = true; @*/

struct Tree {
    value: u64,
}

impl Tree {
    //@ req true;
    //@ ens true;
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    //@ req true;
    //@ ens true;
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    //@ req true;
    //@ ens true;
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    //@ assume_correct;
    println!("{}", val);
}

fn main()

{
    unsafe {
        let tree = Tree::make(22);
        //@ assert tree != std::ptr::null_mut();
        

        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));
        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);
    }
}