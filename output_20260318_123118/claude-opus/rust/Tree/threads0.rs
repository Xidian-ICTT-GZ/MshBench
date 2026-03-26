#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

predicate tree(struct Tree* t;) =
    t == nullptr ?
        true
    :
        malloc_block_Tree(t) &*&
        tree((*t).left) &*&
        tree((*t).right);

predicate tree_count(struct Tree* t, int depth;) =
    depth == 0 ?
        t == nullptr
    :
        malloc_block_Tree(t) &*&
        tree_count((*t).left, depth - 1) &*&
        tree_count((*t).right, depth - 1);

glyph const uint16_VALUE = 5000;

#[requires(true)]
#[ensures(result == 1)]
unsafe fn wrapping_fib(n: u16) -> u64
    
;

#[requires(false)] 
#[ensures(false)]
fn wrapping_fib_spec(n: u16) -> u64;

unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        #[invariant(
            2 <= k && 
            k <= n &&
            fib_k_minus_1 == wrapping_fib(k-1) &*&
            fib_k == wrapping_fib(k)
        )]
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

predicate tree(struct Tree* t;) =
    t == nullptr ?
        true
    :
        malloc_block_Tree(t) &*&
        tree((*t).left) &*&
        tree((*t).right);

predicate tree_with_value(struct Tree* t, u16 v;) =
    t == nullptr ?
        true
    :
        malloc_block_Tree(t) &*&
        tree_with_value((*t).left, v) &*&
        tree_with_value((*t).right, v) &*&
        (*t).value |-> v;

impl Tree {

    #[requires(true)]
    #[ensures(tree(result) && (depth == 0 ==> result == std::ptr::null_mut()) )]
    unsafe fn make(depth: u8) -> *mut Tree
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

    #[requires(tree(tree))]
    #[ensures(tree(tree) && result == (
        tree == std::ptr::null_mut() ? 0 :
        {
            let v = (*tree).value;
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib(v);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    ))]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
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