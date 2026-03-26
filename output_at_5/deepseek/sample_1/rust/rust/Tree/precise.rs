#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout, dealloc}, thread::JoinHandle};

//@ predicate Tree_own(?t) = t.left |-> ?l &*& t.right |-> ?r &*& t.value |-> ?v &*& Tree(l) &*& Tree(r);
//@ predicate Tree(?p) = p == 0 ? true : struct_Tree_padding(p) &*& Tree_own(*p);

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ predicate Sendable_own<T>(?s) = s.payload |-> ?p &*& T(p);
//@ predicate Sendable<T>(?p) = struct_Sendable_padding(p) &*& Sendable_own<T>(*p);

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
//@ req true;
//@ ens true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
//@ req true;
//@ ens true;
{
    h.join().unwrap().payload
}

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

impl Tree {
    unsafe fn make(depth: u8) -> *mut Tree
    //@ req true;
    //@ ens Tree(result);
    {
        if depth == 0 {
            //@ close Tree(0);
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000; 
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ close Tree_own(Tree { left, right, value });
            //@ close Tree(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req Tree(tree);
    //@ ens Tree(tree);
    {
        if tree.is_null() {
            //@ open Tree(0);
            //@ close Tree(0);
            0
        } else {
            //@ open Tree(tree);
            //@ open Tree_own(*tree);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close Tree_own(*tree);
            //@ close Tree(tree);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
    
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req Tree(tree);
    //@ ens Tree(tree);
    {
        if tree.is_null() {
            //@ open Tree(0);
            //@ close Tree(0);
            1
        } else {
            //@ open Tree(tree);
            //@ open Tree_own(*tree);
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close Tree_own(*tree);
            //@ close Tree(tree);
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
    
    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree);
    //@ ens true;
    {
        if !tree.is_null() {
            //@ open Tree(tree);
            //@ open Tree_own(*tree);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        } else {
            //@ open Tree(0);
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
        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        
        let product = join(product_join_handle);
        
        Tree::dispose(tree);
        
        print_u64(sum);
        print_u64(product);
    }
}