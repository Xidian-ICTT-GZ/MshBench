#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

#[predicate]
fn wrapping_fib_pre(n: u16) -> bool {
    true
}

#[predicate]
fn wrapping_fib_post(n: u16, result: u64) -> bool {
    true
}

unsafe fn wrapping_fib(n: u16) -> u64
#[requires(wrapping_fib_pre(n))]
#[ensures(wrapping_fib_post(n, result))]
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(true)]
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

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: u16) -> bool {
    struct_Tree_left(t, left) &&
    struct_Tree_right(t, right) &&
    struct_Tree_value(t, value)
}

#[predicate]
fn tree_own(t: *mut Tree, depth: u8) -> bool {
    if t.is_null() {
        depth == 0
    } else {
        exists![left: *mut Tree, right: *mut Tree, value: u16 |
            tree_points_to(t, left, right, value) &&
            tree_own(left, depth-1) &&
            tree_own(right, depth-1) &&
            depth > 0
        ]
    }
}

#[predicate]
fn tree_own_full(t: *mut Tree) -> bool {
    exists![depth: u8 | tree_own(t, depth)]
}

impl Tree {
    #[predicate]
    fn make_pre(depth: u8) -> bool {
        true
    }
    
    #[predicate]
    fn make_post(depth: u8, result: *mut Tree) -> bool {
        tree_own(result, depth)
    }

    unsafe fn make(depth: u8) -> *mut Tree
    #[requires(Self::make_pre(depth))]
    #[ensures(Self::make_post(depth, result))]
    {
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

    #[predicate]
    fn compute_sum_fibs_pre(tree: *mut Tree) -> bool {
        tree_own_full(tree)
    }
    
    #[predicate]
    fn compute_sum_fibs_post(tree: *mut Tree, result: u64) -> bool {
        tree_own_full(tree)
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    #[requires(Self::compute_sum_fibs_pre(tree))]
    #[ensures(Self::compute_sum_fibs_post(tree, result))]
    {
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

#[predicate]
fn print_u64_pre(value: u64) -> bool {
    true
}

#[predicate]
fn print_u64_post(value: u64) -> bool {
    true
}

unsafe fn print_u64(value: u64)
#[requires(print_u64_pre(value))]
#[ensures(print_u64_post(value))]
{
    println!("{}", value);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_fibs(tree);
        print_u64(sum)
    }
}