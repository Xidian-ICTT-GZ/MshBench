use std::thread;

struct Tree {
    value: u64,
}

/*@

pred Tree_share(t: *mut Tree; value: u64) =
    (*t).value |-> value;

pred Tree_frac(t: *mut Tree, frac: real; value: u64) =
    [frac](*t).value |-> value;

pred_ctor sum_thread_pre(t: *mut Tree, value: u64)() =
    Tree_frac(t, 1/2, value);

pred_ctor sum_thread_post(t: *mut Tree, value: u64)(result: u64) =
    Tree_frac(t, 1/2, value) &*& result == value + 1;

pred_ctor product_thread_pre(t: *mut Tree, value: u64)() =
    Tree_frac(t, 1/2, value);

pred_ctor product_thread_post(t: *mut Tree, value: u64)(result: u64) =
    Tree_frac(t, 1/2, value) &*& result == value + 2;

@*/

impl Tree {
    #[ensures(result != 0 as *mut Tree)]
    #[ensures(Tree_share(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(Tree_frac(tree, 1/2, ?value))]
    #[ensures(Tree_frac(tree, 1/2, value))]
    #[ensures(result == value + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(Tree_frac(tree, 1/2, ?value))]
    #[ensures(Tree_frac(tree, 1/2, value))]
    #[ensures(result == value + 2)]
    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        //@ open Tree_share(tree, 22);
        //@ close Tree_frac(tree, 1/2, 22);
        //@ close Tree_frac(tree, 1/2, 22);

        //@ close sum_thread_pre(tree, 22)();
        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));

        //@ close product_thread_pre(tree, 22)();
        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        let sum = sum_join_handle.join().unwrap();
        //@ open sum_thread_post(tree, 22)(sum);

        let product = product_join_handle.join().unwrap();
        //@ open product_thread_post(tree, 22)(product);

        //@ open Tree_frac(tree, 1/2, 22);
        //@ open Tree_frac(tree, 1/2, 22);

        print_u64(sum);
        print_u64(product);
    }
}