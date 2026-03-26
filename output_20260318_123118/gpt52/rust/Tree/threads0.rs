#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

unsafe fn wrapping_fib(n: u16) -> u64
//@ requires true;
//@ ensures true;
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ invariant 2 <= k && k <= n + 1;
            //@ invariant true;
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

predicate tree(node: *mut Tree) =
    node == std::ptr::null_mut() ?
        emp
    :
        (*node).left |-> ?l &*&
        (*node).right |-> ?r &*&
        (*node).value |-> ?v &*&
        tree(l) &*& tree(r);

@*/

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    //@ requires true;
    //@ ensures tree(result);
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
            //@ close tree(t); // temporarily close? will open to assign fields
            //@ open tree(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ requires tree(tree);
    //@ ensures tree(tree);
    {
        if tree.is_null() {
            0
        } else {
            //@ open tree(tree);
            let left_ptr = (*tree).left;
            let right_ptr = (*tree).right;
            let v = (*tree).value;
            let left_sum = Self::compute_sum_fibs(left_ptr);
            let f = wrapping_fib(v);
            let right_sum = Self::compute_sum_fibs(right_ptr);
            //@ close tree(tree);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

}

unsafe fn print_u64(value: u64)
//@ requires true;
//@ ensures true;
{
    println!("{}", value);
}

fn main()
//@ requires true;
//@ ensures true;
{
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_fibs(tree);
        print_u64(sum)
    }
}