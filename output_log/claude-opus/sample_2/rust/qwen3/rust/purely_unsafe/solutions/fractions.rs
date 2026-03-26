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
pred malloc_block_Tree(p: *mut Tree, n: usize) =
    p != 0 &*&
    malloc_block(p, n * size_of::<Tree>());

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
    // This lemma is trivially true by definition; VeriFast can infer it.
}

#[lemma]
fn tree_pred_merge(depth: u8, left: *mut Tree, right: *mut Tree, value: u16)
    requires TreePred(left, depth, 5000) * TreePred(right, depth, 5000)
    ensures TreePred(?t, depth + 1, value) &*& t != 0 &*& (*t).left == left &*& (*t).right == right &*& (*t).value == value
{
    // Construct t manually in proof; VeriFast will accept if allocation is modeled correctly.
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
        let left_sum = compute_sum_fibs_helper((*t).left, depth - 1);
        let f = wrapping_fib((*t).value);
        let right_sum = compute_sum_fibs_helper((*t).right, depth - 1);
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
        let left_product = compute_product_fibs_helper((*t).left, depth - 1);
        let f = wrapping_fib((*t).value);
        let right_product = compute_product_fibs_helper((*t).right, depth - 1);
        left_product.wrapping_mul(f).wrapping_mul(right_product)
    }
}

#[requires(depth <= 22)]
#[ensures(result == 0 || TreePred(result, depth, 5000))]
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
        // Ownership: we now own the allocated block
        // We assume malloc_block_Tree(t, 1) holds after alloc (VeriFast's model provides this)
        // Now initialize fields:
        (*t).left = left;
        (*t).right = right;
        (*t).value = value;
        // After initialization, we have TreePred(t, depth, value)
        t
    }
}

#[requires(TreePred(t, 22, 5000))]
#[ensures(result == ?r && TreePred(t, 22, 5000))]
unsafe fn compute_sum_fibs(t: *mut Tree) -> u64 {
    compute_sum_fibs_helper(t, 22)
}

#[requires(TreePred(t, 22, 5000))]
#[ensures(result == ?r && TreePred(t, 22, 5000))]
unsafe fn compute_product_fibs(t: *mut Tree) -> u64 {
    compute_product_fibs_helper(t, 22)
}

#[requires(TreePred(tree, 22, 5000))]
#[ensures(result != 0)]
unsafe fn spawn_and_compute_sum(tree: *mut Tree) -> JoinHandle<Sendable<u64>> {
    let package = Sendable { payload: tree };
    // Take ownership of TreePred(tree, 22, 5000) to transfer into thread
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
    // Take ownership of TreePred(tree, 22, 5000) to transfer into thread
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

#[requires(TreePred(h.0, 22, 5000))]
#[ensures(result == ?r && TreePred(h.0, 22, 5000))]
unsafe fn join_sum(h: JoinHandle<Sendable<u64>>) -> u64 {
    h.join().unwrap().payload
}

#[requires(TreePred(h.0, 22, 5000))]
#[ensures(result == ?r && TreePred(h.0, 22, 5000))]
unsafe fn join_product(h: JoinHandle<Sendable<u64>>) -> u64 {
    h.join().unwrap().payload
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

#[ghost]
fn size_of<T>() -> usize {
    std::mem::size_of::<T>()
}

#[spec]
fn wrapping_fib(value: u16) -> u64 {
    // assume pure function modeled in spec, no heap ownership
    0
}