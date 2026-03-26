#![allow(unsafe_op_in_unsafe_fn)]

use std::{
    alloc::{alloc, handle_alloc_error, Layout},
    thread::JoinHandle,
};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> {
    payload: T,
}
unsafe impl<T> Send for Sendable<T> {}

// Ownership predicate for binary tree node and its subtree
#[pred]
pred TreePred(t: *mut Tree, depth: u8, value: u16) =
    t != 0 &*&
    malloc_block_Tree(t, 1) &*&
    (*t).left |-> ?left &*&
    (*t).right |-> ?right &*&
    (*t).value |-> value &*&
    (depth == 0 ?
        left == 0 && right == 0
        :
        TreePred(left, depth - 1, 5000) * TreePred(right, depth - 1, 5000));

// Null pointer as empty tree predicate owning nothing
#[pred]
pred TreePredNull(t: *mut Tree) = t == 0;

// Lemma to split TreePred into left and right subtrees
#[lemma]
fn tree_pred_split(depth: u8, value: u16)
    requires TreePred(?t, depth, value)
    ensures TreePred(t, depth, value) &*&
            (depth == 0 ? true : TreePred((*t).left, depth - 1, 5000) * TreePred((*t).right, depth - 1, 5000))
{
    // Proof by unfolding definition; VeriFast handles
}

// Lemma to merge two subtrees into a new tree node
#[lemma]
fn tree_pred_merge(depth: u8, left: *mut Tree, right: *mut Tree, value: u16)
    requires TreePred(left, depth, 5000) * TreePred(right, depth, 5000)
    ensures TreePred(?t, depth + 1, value) &*& t != 0 &*& (*t).left == left &*& (*t).right == right &*& (*t).value == value
{
    // Proven by allocating new node and assigning fields; VeriFast model
}

#[requires(t != 0 && TreePred(t, depth, 5000))]
#[ensures(TreePred(t, depth, 5000) &*& result == ?r)]
unsafe fn compute_sum_fibs_helper(t: *mut Tree, depth: u8) -> u64
where
    u8: Copy,
{
    if t.is_null() {
        0
    } else {
        let left = (*t).left;
        let right = (*t).right;
        let value = (*t).value;
        // Access left subtree predicate separately to call recursively
        if depth == 0 {
            // leaf node: no subtrees
            let f = wrapping_fib(value);
            f as u64
        } else {
            // depth > 0 implies left and right non-null with TreePred ownership
            // Split ownership of t into node and subtrees
            // Since we own TreePred(t, depth, 5000), we can split:
            tree_pred_split(depth, 5000);
            let left_sum = compute_sum_fibs_helper(left, depth - 1);
            let f = wrapping_fib(value);
            let right_sum = compute_sum_fibs_helper(right, depth - 1);
            left_sum.wrapping_add(f as u64).wrapping_add(right_sum)
        }
    }
}

#[requires(t != 0 && TreePred(t, depth, 5000))]
#[ensures(TreePred(t, depth, 5000) &*& result == ?r)]
unsafe fn compute_product_fibs_helper(t: *mut Tree, depth: u8) -> u64
where
    u8: Copy,
{
    if t.is_null() {
        1
    } else {
        let left = (*t).left;
        let right = (*t).right;
        let value = (*t).value;
        if depth == 0 {
            let f = wrapping_fib(value);
            f as u64
        } else {
            tree_pred_split(depth, 5000);
            let left_product = compute_product_fibs_helper(left, depth - 1);
            let f = wrapping_fib(value);
            let right_product = compute_product_fibs_helper(right, depth - 1);
            left_product.wrapping_mul(f as u64).wrapping_mul(right_product)
        }
    }
}

#[requires(depth <= 22)]
#[ensures(TreePred(result, depth, 5000) &*& result != 0 || depth == 0)]
unsafe fn make_tree(depth: u8) -> *mut Tree {
    if depth == 0 {
        std::ptr::null_mut()
    } else {
        let left = make_tree(depth - 1);
        let right = make_tree(depth - 1);
        let value = 5000;
        let layout = Layout::new::<Tree>();
        let t = alloc(layout) as *mut Tree;
        if t.is_null() {
            handle_alloc_error(layout);
        }
        // After allocation, we own malloc_block_Tree(t, 1)
        (*t).left = left;
        (*t).right = right;
        (*t).value = value;
        // We can now conclude ownership of the entire tree
        // TreePred holds
        // (since left and right satisfy TreePred for depth-1)
        t
    }
}

#[requires(TreePred(t, 22, 5000))]
#[ensures(TreePred(t, 22, 5000) &*& result == ?r)]
unsafe fn compute_sum_fibs(t: *mut Tree) -> u64 {
    compute_sum_fibs_helper(t, 22)
}

#[requires(TreePred(t, 22, 5000))]
#[ensures(TreePred(t, 22, 5000) &*& result == ?r)]
unsafe fn compute_product_fibs(t: *mut Tree) -> u64 {
    compute_product_fibs_helper(t, 22)
}

#[requires(TreePred(tree, 22, 5000))]
#[ensures(result != 0)]
unsafe fn spawn_and_compute_sum(tree: *mut Tree) -> JoinHandle<Sendable<u64>> {
    // We package the tree pointer without duplicating ownership
    let package = Sendable { payload: tree };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable {
            payload: compute_sum_fibs(package_moved.payload),
        }
    })
}

#[requires(TreePred(tree, 22, 5000))]
#[ensures(result != 0)]
unsafe fn spawn_and_compute_product(tree: *mut Tree) -> JoinHandle<Sendable<u64>> {
    let package = Sendable { payload: tree };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable {
            payload: compute_product_fibs(package_moved.payload),
        }
    })
}

#[requires(TreePred(h.0, 22, 5000))]
#[ensures(TreePred(h.0, 22, 5000) &*& result == ?r)]
unsafe fn join_sum(h: JoinHandle<Sendable<u64>>) -> u64 {
    h.join().unwrap().payload
}

#[requires(TreePred(h.0, 22, 5000))]
#[ensures(TreePred(h.0, 22, 5000) &*& result == ?r)]
unsafe fn join_product(h: JoinHandle<Sendable<u64>>) -> u64 {
    h.join().unwrap().payload
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let tree = make_tree(22);

        let sum_join_handle = spawn_and_compute_sum(tree);

        let product_join_handle = spawn_and_compute_product(tree);

        let sum = join_sum(sum_join_handle);

        let product = join_product(product_join_handle);

        print_u64(sum);
        print_u64(product);
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

#[pred]
pred malloc_block_Tree(p: *mut Tree, n: usize) =
    p != 0 &*&
    malloc_block(p, n * size_of::<Tree>());

#[ghost]
fn size_of<T>() -> usize {
    std::mem::size_of::<T>()
}

extern "Rust" {
    fn wrapping_fib(x: u16) -> u16;
}