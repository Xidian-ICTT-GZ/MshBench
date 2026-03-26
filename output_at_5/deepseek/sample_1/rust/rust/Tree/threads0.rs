#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

unsafe fn wrapping_fib(n: u16) -> u64
//@ req true;
//@ ens true;
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv true;
            
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

predicate tree(t: *mut Tree; depth: u8) {
    if t.is_null() {
        depth == 0
    } else {
        alloc::loc(t, 1) &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?val &*&
        tree(left, depth - 1) &*&
        tree(right, depth - 1) &*&
        depth > 0
    }
}

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    //@ req depth <= 255;
    //@ ens tree(result, depth);
    {
        if depth == 0 {
            //@ close tree(std::ptr::null_mut(), 0);
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000; 
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ close_struct(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t, depth);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?depth);
    //@ ens tree(tree, depth) &*& true;
    {
        if tree.is_null() {
            //@ open tree(tree, _);
            0
        } else {
            //@ open tree(tree, depth);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree(tree, depth);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

}

unsafe fn print_u64(value: u64)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_fibs(tree);
        //@ leak tree(tree, _);
        print_u64(sum)
    }
}