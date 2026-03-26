#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

/*@

pred Tree(ptr: *mut Tree; depth: u8) =
    if depth == 0 {
        ptr == std::ptr::null_mut()
    } else {
        (*ptr).left |-> ?left &*&
        (*ptr).right |-> ?right &*&
        (*ptr).value |-> ?value &*&
        struct_Tree_padding(ptr) &*&
        alloc_block(ptr as *mut u8, std::alloc::Layout::new_::<Tree>()) &*&
        Tree(left, depth - 1) &*&
        Tree(right, depth - 1)
    };

lem Tree_inv()
    req Tree(?ptr, ?depth);
    ens Tree(ptr, depth) &*& (depth == 0) == (ptr == std::ptr::null_mut());
{
    open Tree(ptr, depth);
    close Tree(ptr, depth);
}

@*/

#[requires(n <= 1 || n > 1)]
#[ensures(true)]
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv k >= 2 &*& k <= n;
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

    #[requires(depth <= 22)]
    #[ensures(Tree(result, depth))]
    unsafe fn make(depth: u8) -> *mut Tree {
        if depth == 0 {
            //@ close Tree(std::ptr::null_mut(), 0u8);
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value: u16 = 5000;
            let layout = Layout::new::<Tree>();
            let t = alloc(layout) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(layout);
            }
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close Tree(t, depth);
            t
        }
    }

    #[requires(Tree(tree, ?d))]
    #[ensures(Tree(tree, d))]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64 {
        //@ open Tree(tree, d);
        if tree.is_null() {
            //@ close Tree(tree, d);
            0
        } else {
            let left_ptr = (*tree).left;
            let right_ptr = (*tree).right;
            let val = (*tree).value;
            let left_sum = Self::compute_sum_fibs(left_ptr);
            let f = wrapping_fib(val);
            let right_sum = Self::compute_sum_fibs(right_ptr);
            //@ close Tree(tree, d);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
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