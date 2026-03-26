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

/*@

pred Tree(t: *mut Tree;) =
    if t == 0 {
        true
    } else {
        (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> ?value &*&
        struct_Tree_padding(t) &*&
        Tree(left) &*& Tree(right)
    };

@*/

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    //@ req true;
    //@ ens Tree(result);
    {
        if depth == 0 {
            //@ close Tree(std::ptr::null_mut());
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
            //@ close Tree(t);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req Tree(tree);
    //@ ens Tree(tree);
    {
        if tree.is_null() {
            //@ open Tree(tree);
            //@ close Tree(tree);
            0
        } else {
            //@ open Tree(tree);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close Tree(tree);
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
        //@ leak Tree(tree);
        print_u64(sum)
    }
}