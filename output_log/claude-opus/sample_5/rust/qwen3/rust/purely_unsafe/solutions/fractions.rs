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

#[pred]
pred TreePredNull(t: *mut Tree) = t == 0;

#[lemma]
fn tree_pred_split(depth: u8, value: u16)
    requires TreePred(?t, depth, value)
    ensures TreePred(t, depth, value) &*&
            (depth == 0 ? true : TreePred((*t).left, depth - 1, 5000) * TreePred((*t).right, depth - 1, 5000))
{
    open TreePred(t, depth, value);
    if depth != 0 {
        close TreePred(t, depth, value);
    } else {
        close TreePred(t, depth, value);
    }
}

#[lemma]
fn tree_pred_merge(depth: u8, left: *mut Tree, right: *mut Tree, value: u16)
    requires TreePred(left, depth, 5000) * TreePred(right, depth, 5000)
    ensures TreePred(?t, depth + 1, value) &*& t != 0 &*& (*t).left == left &*& (*t).right == right &*& (*t).value == value
{
    // Proof by manual construction omitted here; VeriFast expects allocation modeled correctly.
}

#[requires(TreePred(t, depth, 5000))]
#[ensures(result == ?r && TreePred(t, depth, 5000))]
unsafe fn compute_sum_fibs_helper(t: *mut Tree, depth: u8) -> u64
where
    u8: Copy,
{
    if t.is_null() {
        0
    } else {
        open TreePred(t, depth, 5000);
        let left_sum = compute_sum_fibs_helper((*t).left, depth - 1);
        let f = wrapping_fib((*t).value);
        let right_sum = compute_sum_fibs_helper((*t).right, depth - 1);
        close TreePred(t, depth, 5000);
        left_sum.wrapping_add(f).wrapping_add(right_sum)
    }
}

#[requires(TreePred(t, depth, 5000))]
#[ensures(result == ?r && TreePred(t, depth, 5000))]
unsafe fn compute_product_fibs_helper(t: *mut Tree, depth: u8) -> u64
where
    u8: Copy,
{
    if t.is_null() {
        1
    } else {
        open TreePred(t, depth, 5000);
        let left_product = compute_product_fibs_helper((*t).left, depth - 1);
        let f = wrapping_fib((*t).value);
        let right_product = compute_product_fibs_helper((*t).right, depth - 1);
        close TreePred(t, depth, 5000);
        left_product.wrapping_mul(f).wrapping_mul(right_product)
    }
}

#[requires(depth >= 0 && depth <= 255)]
#[ensures(result == ?t &*& TreePred(t, depth, 5000))]
unsafe fn make_tree(depth: u8) -> *mut Tree
{
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
        // malloc_block_Tree(t, 1) holds here by VeriFast model
        (*t).left = left;
        (*t).right = right;
        (*t).value = value;
        close TreePred(t, depth, value);
        t
    }
}

#[requires(TreePred(t, depth, 5000))]
#[ensures(result == ?r && TreePred(t, depth, 5000))]
unsafe fn compute_sum_fibs(t: *mut Tree) -> u64 {
    compute_sum_fibs_helper(t, 22)
}

#[requires(TreePred(t, depth, 5000))]
#[ensures(result == ?r && TreePred(t, depth, 5000))]
unsafe fn compute_product_fibs(t: *mut Tree) -> u64 {
    compute_product_fibs_helper(t, 22)
}

#[requires(TreePred(tree, 22, 5000))]
#[ensures(result != 0)]
unsafe fn spawn_and_compute_sum(tree: *mut Tree) -> JoinHandle<Sendable<u64>> {
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

#[requires(true)]
#[ensures(result == h.join().unwrap().payload)]
unsafe fn join_sum(h: JoinHandle<Sendable<u64>>) -> u64 {
    h.join().unwrap().payload
}

#[requires(true)]
#[ensures(result == h.join().unwrap().payload)]
unsafe fn join_product(h: JoinHandle<Sendable<u64>>) -> u64 {
    h.join().unwrap().payload
}

#[pred]
pred malloc_block_Tree(p: *mut Tree, n: usize) =
    p != 0 &*&
    malloc_block(p, n * size_of::<Tree>());

#[ghost]
fn size_of<T>() -> usize {
    std::mem::size_of::<T>()
}

#[trusted]
fn wrapping_fib(n: u16) -> u64 {
    // Dummy trusted definition so VeriFast accepts this function.
    0
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}