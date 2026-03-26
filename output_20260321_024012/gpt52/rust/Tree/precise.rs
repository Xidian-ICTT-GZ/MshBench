#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout, dealloc}, thread::JoinHandle};

/*@

pred tree(t: *mut Tree) =
    t == std::ptr::null_mut() ?
        true
    :
        (*t).left |-> ?l &*& (*t).right |-> ?r &*& (*t).value |-> ?v &*&
        tree(l) &*& tree(r) &*&
        std::alloc::alloc_block(t as *mut u8, Layout::new::<Tree>());

@*/

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

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
            //@ inv 2 <= k &*& k <= n &*& true;
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
    //@ ens tree(result);
    {
        if depth == 0 {
            //@ close tree(std::ptr::null_mut());
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000; 
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ std::alloc::alloc_block(t as *mut u8, Layout::new::<Tree>());
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree);
    //@ ens tree(tree);
    {
        if tree.is_null() {
            //@ open tree(tree);
            //@ close tree(tree);
            0
        } else {
            //@ open tree(tree);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree(tree);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
    
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree);
    //@ ens tree(tree);
    {
        if tree.is_null() {
            //@ open tree(tree);
            //@ close tree(tree);
            1
        } else {
            //@ open tree(tree);
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close tree(tree);
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
    
    unsafe fn dispose(tree: *mut Tree)
    //@ req tree(tree);
    //@ ens true;
    {
        if !tree.is_null() {
            //@ open tree(tree);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            //@ open std::alloc::alloc_block(tree as *mut u8, Layout::new::<Tree>());
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        } else {
            //@ open tree(tree);
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
{
    unsafe {
        let tree = Tree::make(22);
        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        
        let product = join(product_join_handle);
        
        //@ open tree(tree);
        //@ close tree(tree);
        Tree::dispose(tree);
        
        print_u64(sum);
        print_u64(product);
    }
}