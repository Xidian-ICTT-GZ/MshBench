//@ pred Tree(t: *mut Tree; depth: nat) = 
//@   t == 0 ? true :
//@   (*t).left |-> ?l &*& (*t).right |-> ?r &*& (*t).value |-> _ &*&
//@   Tree(l, ?d1) &*& Tree(r, ?d2) &*& depth == d1 + 1 &*& depth == d2 + 1;

//@ pred Sendable_own<T>(s: *Sendable<T>) = *s |-> ?x;

//@ lemma void Sendable_own_split<T>(s: *Sendable<T>)
//@   req Sendable_own(s);
//@   ens Sendable_own(s);
//@ {
//@ }

//@ lemma void Sendable_own_join<T>(s: *Sendable<T>)
//@   req Sendable_own(s);
//@   ens Sendable_own(s);
//@ {
//@ }

#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ req true;
//@ ens true;
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static

{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

//@ req true;
//@ ens true;
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R

{
    h.join().unwrap().payload
}

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

    //@ req depth == 0 ? true : true;
    //@ ens Tree(result, depth);
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
            //@ close Tree(left, _);
            //@ close Tree(right, _);
            //@ assert Tree(left, ?dl);
            //@ assert Tree(right, ?dr);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close Tree(t, depth);
            
            t
        }
    }

    //@ req Tree(tree, ?d);
    //@ ens Tree(tree, d) &*& result == _;
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    
    
    {
        if tree.is_null() {
            0
        } else {
            //@ open Tree(tree, ?d);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close Tree(tree, d);
            
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
    
    //@ req Tree(tree, ?d);
    //@ ens Tree(tree, d) &*& result == _;
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    
    
    {
        if tree.is_null() {
            1
        } else {
            //@ open Tree(tree, ?d);
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close Tree(tree, d);
            
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
    
}

//@ req true;
//@ ens true;
unsafe fn print_u64(value: u64)

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
        
        
        
        print_u64(sum);
        print_u64(product);
    }
}