#![allow(unsafe_op_in_unsafe_fn)]
use std::{
    alloc::{alloc, handle_alloc_error, Layout},
};

/*@

pred tree(t: *mut Tree, depth: u8) =
    if t == std::ptr::null_mut() {
        depth == 0
    } else {
        depth > 0 &*&
        alloc_block_Tree(t) &*&
        (*t).left |-> ?l &*&
        (*t).right |-> ?r &*&
        (*t).value |-> ?v &*&
        tree(l, (depth - 1) as u8) &*&
        tree(r, (depth - 1) as u8)
    };

@*/

//@ req true;
//@ ens true;
unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv true;
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

impl Tree {
    //@ req true;
    //@ ens tree(result, depth);
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
            //@ close alloc_block_Tree(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t, depth);
            t
        }
    }

    //@ req tree(tree, ?d);
    //@ ens tree(tree, d);
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    {
        if tree.is_null() {
            0
        } else {
            //@ open tree(tree, d);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree(tree, d);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
}

//@ req true;
//@ ens true;
unsafe fn print_u64(value: u64)
{
    //@ assume_correct
    println!("{}", value);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        //@ open tree(tree, 22);
        //@ close tree(tree, 22);
        let sum = Tree::compute_sum_fibs(tree);
        //@ open tree(tree, 22);
        //@ close tree(tree, 22);
        print_u64(sum)
    }
}