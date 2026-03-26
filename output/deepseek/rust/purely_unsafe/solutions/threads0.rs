#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: u16) -> bool {
    unsafe { (*t).left == left && (*t).right == right && (*t).value == value }
}

#[predicate]
fn tree_full(t: *mut Tree) -> bool {
    !t.is_null() && exists![left: *mut Tree, right: *mut Tree, value: u16;
        tree_points_to(t, left, right, value) && tree_full(left) && tree_full(right)
    ]
}

#[predicate]
fn tree_full_with_depth(t: *mut Tree, depth: u8) -> bool {
    if depth == 0 {
        t.is_null()
    } else {
        !t.is_null() && exists![left: *mut Tree, right: *mut Tree, value: u16;
            tree_points_to(t, left, right, value) && 
            tree_full_with_depth(left, depth - 1) && 
            tree_full_with_depth(right, depth - 1)
        ]
    }
}

#[predicate]
fn tree_full_with_depth_and_value(t: *mut Tree, depth: u8, value: u16) -> bool {
    if depth == 0 {
        t.is_null()
    } else {
        !t.is_null() && exists![left: *mut Tree, right: *mut Tree;
            tree_points_to(t, left, right, value) && 
            tree_full_with_depth_and_value(left, depth - 1, value) && 
            tree_full_with_depth_and_value(right, depth - 1, value)
        ]
    }
}

#[predicate]
fn tree_full_with_depth_and_value_constant(t: *mut Tree, depth: u8) -> bool {
    tree_full_with_depth_and_value(t, depth, 5000)
}

#[predicate]
fn tree_full_with_depth_and_value_constant_allocated(t: *mut Tree, depth: u8) -> bool {
    tree_full_with_depth_and_value_constant(t, depth) && 
    exists![layout: Layout; layout == Layout::new::<Tree>()]
}

unsafe fn wrapping_fib(n: u16) -> u64
#[requires(n <= 5000)]
#[ensures(result <= 18446744073709551615u64)]
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(k >= 2 && k <= n)]
        #[invariant(fib_k_minus_1 <= 18446744073709551615u64)]
        #[invariant(fib_k <= 18446744073709551615u64)]
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
    unsafe fn make(depth: u8) -> *mut Tree
    #[requires(depth <= 22)]
    #[ensures(tree_full_with_depth_and_value_constant(result, depth))]
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

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    #[requires(tree_full(tree))]
    #[ensures(result <= 18446744073709551615u64)]
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

unsafe fn print_u64(value: u64)
#[requires(value <= 18446744073709551615u64)]
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