#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

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

//@ predicate tree(t: *mut Tree; depth: u8) = 
//@     if t.is_null() {
//@         depth == 0
//@     } else {
//@         alloc::malloc_block(t, std::mem::size_of::<Tree>()) &*&
//@         (*t).left |-> ?left &*&
//@         (*t).right |-> ?right &*&
//@         (*t).value |-> ?val &*&
//@         tree(left, depth - 1) &*&
//@         tree(right, depth - 1) &*&
//@         depth > 0
//@     };

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    //@ req depth >= 0;
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
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t, depth);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?depth);
    //@ ens tree(tree, depth);
    {
        if tree.is_null() {
            //@ open tree(std::ptr::null_mut(), _);
            //@ close tree(std::ptr::null_mut(), _);
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
        //@ open tree(tree, 22);
        let left = (*tree).left;
        let right = (*tree).right;
        //@ close tree(left, 21);
        //@ close tree(right, 21);
        //@ close tree(tree, 22);
        
        let left_join_handle = spawn(Tree::compute_sum_fibs, left);
        
        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);
        
        let right_sum = join(right_join_handle);
        
        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);
        //@ open tree(tree, 22);
        //@ open tree(left, 21);
        //@ open tree(right, 21);
        //@ alloc::leak(t);
        
        print_u64(sum)
    }
}