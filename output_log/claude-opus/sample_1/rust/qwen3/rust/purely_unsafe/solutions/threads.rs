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
fn sendable_pred<T>(t: Sendable<T>) =
    true; // kept as is because no heap ownership to describe for Sendable

#[lemma]
fn sendable_move<T>(t: Sendable<T>) -> () {
    requires(sendable_pred(t));
    ensures(sendable_pred(t));
}

#[pred]
fn join_handle_pred<R>(h: JoinHandle<Sendable<R>>) =
    true; // no heap ownership tracked for JoinHandle

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where
    A: 'static,
    R: 'static,
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable {
            payload: f(package_moved.payload),
        }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
}

#[pred]
fn fib_node_pred(n: u16, r: u64) =  
    n <= 1 ? r == 1 :
    exists<u64,l64>(fib_node_pred(n - 1, l64) &*& fib_node_pred(n - 2, ?l2) &*& r == l64.wrapping_add(l2));

#[pred]
fn fib_pred(n: u16, r: u64) = fib_node_pred(n, r);

unsafe fn wrapping_fib(n: u16) -> u64 {
    #[requires(n <= 20)]
    #[ensures(fib_pred(n, result))]
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(fib_pred(k - 1, fib_k_minus_1))]
        #[invariant(fib_pred(k, fib_k))]
        loop {
            if k == n {
                break;
            }

            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);

            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

predicate tree_node_pred(Tree* p, u8 depth, u64 sum) =
    p != null ==> 
        p->left |-> ?l &*& p->right |-> ?r &*& p->value |-> ?v &*&
        tree_node_pred(l, depth - 1, ?lsum) &*&
        tree_node_pred(r, depth - 1, ?rsum) &*&
        fib_pred(v, ?fv) &*& 
        sum == lsum.wrapping_add(fv).wrapping_add(rsum)
    || (p == null && depth == 0 && sum == 0);

predicate tree_root_pred(Tree* p, u8 depth) =
    p != null ==> 
        p->left |-> ?l &*& p->right |-> ?r &*& p->value |-> ?v &*&
        tree_node_pred(l, depth - 1, ?lsum) &*&
        tree_node_pred(r, depth - 1, ?rsum) &*&
        fib_pred(v, ?fv) &*&
        tree_root_pred(l, depth - 1) &*&
        tree_root_pred(r, depth - 1)
    || (p == null && depth == 0);

impl Tree {
    unsafe fn make(depth: u8) -> *mut Tree {
        #[requires(depth <= 22)]
        #[ensures(result != std::ptr::null_mut() ==> tree_root_pred(result, depth))]
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000;
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;

            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        #[requires(tree != std::ptr::null_mut() ==> tree_node_pred(tree, ?d, ?s))]
        #[ensures(result == ?s)]
        if tree.is_null() {
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);

            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
}

unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);

        let left = (*tree).left;
        let right = (*tree).right;

        let left_join_handle = spawn(Tree::compute_sum_fibs, left);

        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);

        let right_sum = join(right_join_handle);

        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);

        print_u64(sum)
    }
}