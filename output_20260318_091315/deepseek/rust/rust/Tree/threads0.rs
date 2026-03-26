#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

#[predicate]
fn tree(t: *mut Tree, depth: u8) -> bool {
    pearlite! {
        if t.is_null() {
            depth == 0
        } else {
            depth > 0 &&
            exists<d1: u8, d2: u8> d1 == depth-1 && d2 == depth-1 &&
            tree((*t).left, d1) && tree((*t).right, d2) &&
            (*t).value == 5000
        }
    }
}

#[predicate]
fn tree_sum(t: *mut Tree, s: u64) -> bool {
    pearlite! {
        if t.is_null() {
            s == 0
        } else {
            exists<s1: u64, s2: u64, f: u64> 
            tree_sum((*t).left, s1) && 
            tree_sum((*t).right, s2) &&
            f == wrapping_fib((*t).value) &&
            s == s1.wrapping_add(f).wrapping_add(s2)
        }
    }
}

#[requires(n <= 65535)]
#[ensures(result == wrapping_fib(n))]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(fib_k == wrapping_fib(k))]
        #[invariant(fib_k_minus_1 == wrapping_fib(k-1))]
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

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

impl Tree {
    #[requires(depth <= 255)]
    #[ensures(tree(result, depth))]
    unsafe fn make(depth: u8) -> *mut Tree {
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

    #[requires(tree(t, _))]
    #[ensures(tree_sum(t, result))]
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

#[requires(true)]
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