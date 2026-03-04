use std::thread;

/*@
pred_ctor inspect_tree_post(tree: *mut Tree, depth: i32)(result: u64) =
[1/2]Tree(tree, depth);
pred inspect_tree_pre(tree: *mut Tree, post: pred(u64)) =
[1/2]Tree(tree, ?depth) &*& post == inspect_tree_post(tree, depth);
@*/

struct Tree {
    value: u64,
}

impl Tree {
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    fn compute_product_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 2 }
    }
}

fn print_u64(val: u64) {
    println!("{}", val);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = Tree::make(22);
        /*@ produce_fn_ptr_chunk Spawnee<*mut Tree, u64>(Tree::compute_sum_fibs)
        (inspect_tree_pre)(arg) {
            open inspect_tree_pre(arg, _);
            assert [1/2]Tree(arg, ?depth);
            let result = call();
            close inspect_tree_post(arg, depth)(result);
        }
        @*/
        //@ close inspect_tree_pre(tree, _);

        // Rust 线程版 spawn
        let sum_join_handle = thread::spawn(move || Tree::compute_sum_fibs(tree));

        /*@ produce_fn_ptr_chunk Spawnee<*mut Tree, u64>(Tree::compute_product_fibs)
        (inspect_tree_pre)(arg) {
            open inspect_tree_pre(arg, _);
            assert [1/2]Tree(arg, ?depth);
            let result = call();
            close inspect_tree_post(arg, depth)(result);
        }
        @*/
        //@ close inspect_tree_pre(tree, _);

        let product_join_handle = thread::spawn(move || Tree::compute_product_fibs(tree));

        // join 替代
        let sum = sum_join_handle.join().unwrap();
        //@ open inspect_tree_post(tree, 22)(_);
        //@ leak [1/2]Tree(tree, 22);

        let product = product_join_handle.join().unwrap();
        //@ open inspect_tree_post(tree, 22)(_);
        //@ leak [1/2]Tree(tree, 22);

        print_u64(sum);
        print_u64(product);
    }
}
