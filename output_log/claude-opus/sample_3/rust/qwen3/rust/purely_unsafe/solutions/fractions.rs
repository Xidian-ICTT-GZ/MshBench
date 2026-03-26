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

/*@
pred TreePred(t: *mut Tree, depth: u8, value: u16) =
    if depth == 0 {
        t == 0
    } else {
        t != 0 &*&
        struct_Tree_padding(t) &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> value &*&
        TreePred(left, (depth - 1) as u8, 5000u16) &*&
        TreePred(right, (depth - 1) as u8, 5000u16) &*&
        alloc_block(t as *u8, std::mem::size_of::<Tree>())
    };
@*/

/*@
fn_type thread_run_sum(tree_ptr: *mut Tree) = unsafe fn() -> Sendable<u64>
    req TreePred(tree_ptr, 22u8, 5000u16);
    ens TreePred(tree_ptr, 22u8, 5000u16);
@*/

/*@
fn_type thread_run_product(tree_ptr: *mut Tree) = unsafe fn() -> Sendable<u64>
    req TreePred(tree_ptr, 22u8, 5000u16);
    ens TreePred(tree_ptr, 22u8, 5000u16);
@*/

unsafe fn compute_sum_fibs_helper(t: *mut Tree, depth: u8) -> u64
//@ req TreePred(t, depth, 5000u16);
//@ ens TreePred(t, depth, 5000u16);
{
    if depth == 0 {
        //@ open TreePred(t, depth, 5000u16);
        //@ close TreePred(t, depth, 5000u16);
        0
    } else {
        //@ open TreePred(t, depth, 5000u16);
        let left_sum = compute_sum_fibs_helper((*t).left, depth - 1);
        let f = wrapping_fib((*t).value);
        let right_sum = compute_sum_fibs_helper((*t).right, depth - 1);
        //@ close TreePred(t, depth, 5000u16);
        left_sum.wrapping_add(f).wrapping_add(right_sum)
    }
}

unsafe fn compute_product_fibs_helper(t: *mut Tree, depth: u8) -> u64
//@ req TreePred(t, depth, 5000u16);
//@ ens TreePred(t, depth, 5000u16);
{
    if depth == 0 {
        //@ open TreePred(t, depth, 5000u16);
        //@ close TreePred(t, depth, 5000u16);
        1
    } else {
        //@ open TreePred(t, depth, 5000u16);
        let left_product = compute_product_fibs_helper((*t).left, depth - 1);
        let f = wrapping_fib((*t).value);
        let right_product = compute_product_fibs_helper((*t).right, depth - 1);
        //@ close TreePred(t, depth, 5000u16);
        left_product.wrapping_mul(f).wrapping_mul(right_product)
    }
}

unsafe fn make_tree(depth: u8) -> *mut Tree
//@ req true;
//@ ens TreePred(result, depth, 5000u16);
{
    if depth == 0 {
        //@ close TreePred(std::ptr::null_mut(), 0u8, 5000u16);
        std::ptr::null_mut()
    } else {
        let left = make_tree(depth - 1);
        let right = make_tree(depth - 1);
        let value: u16 = 5000;
        let layout = Layout::new::<Tree>();
        let t = alloc(layout) as *mut Tree;
        if t.is_null() {
            handle_alloc_error(layout);
        }
        //@ close_struct(t);
        (*t).left = left;
        (*t).right = right;
        (*t).value = value;
        //@ close TreePred(t, depth, 5000u16);
        t
    }
}

unsafe fn compute_sum_fibs(t: *mut Tree) -> u64
//@ req TreePred(t, 22u8, 5000u16);
//@ ens TreePred(t, 22u8, 5000u16);
{
    compute_sum_fibs_helper(t, 22)
}

unsafe fn compute_product_fibs(t: *mut Tree) -> u64
//@ req TreePred(t, 22u8, 5000u16);
//@ ens TreePred(t, 22u8, 5000u16);
{
    compute_product_fibs_helper(t, 22)
}

unsafe fn print_u64(value: u64)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}

fn wrapping_fib(n: u16) -> u64
//@ req true;
//@ ens true;
{
    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u16 = 0;
    //@ inv true;
    while i < n {
        let c = a.wrapping_add(b);
        a = b;
        b = c;
        i = i + 1;
    }
    a
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = make_tree(22);

        let sum = compute_sum_fibs(tree);

        let product = compute_product_fibs(tree);

        print_u64(sum);
        print_u64(product);
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}