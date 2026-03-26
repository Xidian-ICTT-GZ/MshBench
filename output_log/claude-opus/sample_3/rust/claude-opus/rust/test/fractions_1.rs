use std::thread;

struct Tree {
    value: u64,
}

predicate Tree(t: *mut Tree, v: u64) = 
    struct_Tree_padding(t) &*& (*t).value |-> v;

predicate Tree_share(t: *mut Tree, v: u64) = 
    [1/2]struct_Tree_padding(t) &*& [1/2](*t).value |-> v;

predicate Tree_full(t: *mut Tree, v: u64) = Tree(t, v);

lemma void tree_split(struct_Tree_padding_padding: struct_Tree_padding(t), v: u64)
    requires Tree(t, v);
    ensures Tree_share(t, v) &*& Tree_share(t, v);
{
    open Tree(t, v);
    split_fraction struct_Tree_padding(t) into [1/2] and [1/2];
    split_fraction (*t).value |-> v into [1/2] and [1/2];
    close Tree_share(t, v);
    close Tree_share(t, v);
}

lemma void tree_join()
    requires Tree_share(t, v) &*& Tree_share(t, v);
    ensures Tree(t, v);
{
    open Tree_share(t, v);
    open Tree_share(t, v);
    combine_fraction struct_Tree_padding(t) from [1/2] and [1/2];
    combine_fraction (*t).value |-> v from [1/2] and [1/2];
    close Tree(t, v);
}

impl Tree {
    #[ensures(Tree(result, v))]
    fn make(v: u64) -> *mut Tree {
        Box::into_raw(Box::new(Tree { value: v }))
    }

    #[requires(Tree_share(tree, v))]
    #[ensures(Tree_share(tree, v) &*& result == v + 1)]
    fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        unsafe { (*tree).value + 1 }
    }

    #[requires(Tree_share(tree, v))]
    #[ensures(Tree_share(tree, v) &*& result == v + 2)]
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
        open Tree(tree, 22);
        tree_split();
        close Tree_share(tree, 22);
        close Tree_share(tree, 22);

        let sum_join_handle = thread::spawn(move || {
            Tree::compute_sum_fibs(tree)
        });

        let product_join_handle = thread::spawn(move || {
            Tree::compute_product_fibs(tree)
        });

        let sum = sum_join_handle.join().unwrap();

        let product = product_join_handle.join().unwrap();

        print_u64(sum);
        print_u64(product);

        open Tree_share(tree, 22);
        open Tree_share(tree, 22);
        tree_join();
        close Tree(tree, 22);

        let _ = Box::from_raw(tree);
    }
}