#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

#[predicate]
fn treepred(ptr: *mut Tree, depth: u8) = 
    ptr != std::ptr::null_mut() &*& ptr |-> Tree {left: ?l, right: ?r, value: ?v} &*&
    (depth == 0 ? 
        l == std::ptr::null_mut() &*& r == std::ptr::null_mut()
    : 
        treepred(l, depth - 1) &*& treepred(r, depth - 1)
    );

#[predicate]
fn tree_root(ptr: *mut Tree, depth: u8) = treepred(ptr, depth);

#[requires(n <= 1 ==> true)]
#[ensures(result == 1)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n && fib_k == wrapping_fib(k) && fib_k_minus_1 == wrapping_fib(k - 1))]
        loop {
            if k == n { break; }
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

impl Tree {
    #[requires(depth <= 22)]
    #[ensures(tree_root(result, depth))]
    unsafe fn make(depth: u8) -> *mut Tree {
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let layout = Layout::new::<Tree>();
            let t = alloc(layout) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(layout);
            }
            #[ghost] 
            let _ = ();
            // Write fields with full ownership since alloc returns uninitialized memory
            (*t).left = left;
            (*t).right = right;
            (*t).value = 5000;
            t
        }
    }

    #[requires(tree_root(tree, ?d))]
    #[ensures(result == sum_fibs_tree(tree))]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64 {
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

#[pure]
fn sum_fibs_tree(tree: *mut Tree) -> u64 {
    if tree.is_null() {
        0
    } else {
        let t = unsafe { *tree };
        sum_fibs_tree(t.left) + wrapping_fib(t.value) + sum_fibs_tree(t.right)
    }
}

unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_fibs(tree);
        print_u64(sum)
    }
}