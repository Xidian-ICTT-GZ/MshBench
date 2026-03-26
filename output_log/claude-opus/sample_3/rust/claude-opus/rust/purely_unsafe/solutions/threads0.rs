#![allow(unsafe_op_in_unsafe_fn)]
use std::{alloc::{alloc, handle_alloc_error, Layout}};

/*@

predicate struct_Tree_padding(t: *mut Tree) = alloc_block(t as *mut u8 + 2 * usize::size_of::<*mut Tree>(), 2 * usize::size_of::<u16>());

pred Tree(t: *mut Tree) =
    if t == 0 as *mut Tree {
        emp
    } else {
        (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> ?v &*&
        struct_Tree_padding(t) &*& alloc_block(t as *mut u8, Layout::new_::<Tree>()) &*&
        Tree(left) &*& Tree(right)
    };

lemma void open_struct(struct Tree* t)
    requires alloc_block(t as void*, sizeof(struct Tree));
    ensures (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> ?value &*& struct_Tree_padding(t) &*& alloc_block(t as void*, sizeof(struct Tree));
{
    open alloc_block(t as char*, sizeof(struct Tree));
    // struct_Tree_padding focuses on padding after first two pointers
    close struct_Tree_padding(t);
}

lemma void close_struct(struct Tree* t)
    requires (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> ?value &*& struct_Tree_padding(t);
    ensures alloc_block(t as void*, sizeof(struct Tree));
{
    open struct_Tree_padding(t);
    close alloc_block(t as char*, sizeof(struct Tree));
}

@*/

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
        loop 
        //@ invariant 2 <= k &*& k <= n + 1 &*& fib_k_minus_1 |-> _ &*& fib_k |-> _;
        {
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
    //@ requires true;
    //@ ensures Tree(result);
    {
        if depth == 0 {
            //@ close Tree(0 as *mut Tree);
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000; 
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ open_struct(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close Tree(t);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ requires Tree(tree);
    //@ ensures Tree(tree);
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
        //@ open Tree(tree);
        //@ leak Tree((*tree).left) &*& Tree((*tree).right) &*& (*tree).left |-> _ &*& (*tree).right |-> _ &*& (*tree).value |-> _ &*& struct_Tree_padding(tree) &*& alloc_block(tree as *mut u8, Layout::new::<Tree>());
        print_u64(sum)
    }
}