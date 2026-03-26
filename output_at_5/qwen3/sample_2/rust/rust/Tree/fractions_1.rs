use std::thread;

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    //@ req tree != null;
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    //@ req tree != null;
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
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
            let _ = tree; 
            Tree::compute_sum_fibs(tree)
        });

        let product_join_handle = thread::spawn(move || {
            let _ = tree; 
            Tree::compute_product_fibs(tree)
        });

        let sum = sum_join_handle.join().unwrap();
        
        let product = product_join_handle.join().unwrap();
        
        print_u64(sum);
        print_u64(product);
    }
}