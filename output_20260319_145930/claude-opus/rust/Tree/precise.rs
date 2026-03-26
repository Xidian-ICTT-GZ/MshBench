#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout, dealloc}, thread::JoinHandle};

/*@

pred Tree(t: *mut Tree; depth: i32) =
    if t == 0 {
        depth == 0
    } else {
        alloc_block_Tree(t) &*&
        (*t).left |-> ?left &*&
        (*t).right |-> ?right &*&
        (*t).value |-> ?value &*&
        depth > 0 &*&
        Tree(left, depth - 1) &*&
        Tree(right, depth - 1)
    };

pred Tree_frac(t: *mut Tree, f: real;) =
    if t == 0 {
        true
    } else {
        [f]alloc_block_Tree(t) &*&
        [f](*t).left |-> ?left &*&
        [f](*t).right |-> ?right &*&
        [f](*t).value |-> ?value &*&
        Tree_frac(left, f) &*&
        Tree_frac(right, f)
    };

lem Tree_to_frac(t: *mut Tree)
    req Tree(t, ?depth);
    ens Tree_frac(t, 1r);
{
    if t != 0 {
        open Tree(t, depth);
        Tree_to_frac((*t).left);
        Tree_to_frac((*t).right);
        close Tree_frac(t, 1r);
    } else {
        open Tree(t, depth);
        close Tree_frac(t, 1r);
    }
}

lem Tree_frac_to_full(t: *mut Tree)
    req Tree_frac(t, 1r);
    ens Tree(t, _);
{
    open Tree_frac(t, 1r);
    if t != 0 {
        Tree_frac_to_full((*t).left);
        Tree_frac_to_full((*t).right);
        close Tree(t, _);
    } else {
        close Tree(t, 0);
    }
}

lem Tree_split_frac(t: *mut Tree)
    req Tree_frac(t, ?f);
    ens Tree_frac(t, f/2) &*& Tree_frac(t, f/2);
{
    open Tree_frac(t, f);
    if t != 0 {
        Tree_split_frac((*t).left);
        Tree_split_frac((*t).right);
        close Tree_frac(t, f/2);
        close Tree_frac(t, f/2);
    } else {
        close Tree_frac(t, f/2);
        close Tree_frac(t, f/2);
    }
}

lem Tree_merge_frac(t: *mut Tree)
    req Tree_frac(t, ?f1) &*& Tree_frac(t, ?f2);
    ens Tree_frac(t, f1 + f2);
{
    open Tree_frac(t, f1);
    open Tree_frac(t, f2);
    if t != 0 {
        Tree_merge_frac((*t).left);
        Tree_merge_frac((*t).right);
        close Tree_frac(t, f1 + f2);
    } else {
        close Tree_frac(t, f1 + f2);
    }
}

@*/

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

//@ req true;
//@ ens true;
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    //@ assume_correct
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
    //@ assume_correct
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

    //@ req true;
    //@ ens Tree(result, depth as i32);
    unsafe fn make(depth: u8) -> *mut Tree
    {
        if depth == 0 {
            //@ close Tree(std::ptr::null_mut(), 0);
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
            //@ close Tree(t, depth as i32);
            t
        }
    }

    //@ req Tree_frac(tree, ?f);
    //@ ens Tree_frac(tree, f);
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    {
        //@ open Tree_frac(tree, f);
        if tree.is_null() {
            //@ close Tree_frac(tree, f);
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f_val = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close Tree_frac(tree, f);
            left_sum.wrapping_add(f_val).wrapping_add(right_sum)
        }
    }
    
    //@ req Tree_frac(tree, ?f);
    //@ ens Tree_frac(tree, f);
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    {
        //@ open Tree_frac(tree, f);
        if tree.is_null() {
            //@ close Tree_frac(tree, f);
            1
        } else {
            let left_product = Self::compute_product_fibs((*tree).left);
            let f_val = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close Tree_frac(tree, f);
            left_product.wrapping_mul(f_val).wrapping_mul(right_product)
        }
    }
    
    //@ req Tree(tree, _);
    //@ ens true;
    unsafe fn dispose(tree: *mut Tree)
    {
        //@ open Tree(tree, _);
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
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

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let tree = Tree::make(22);
        //@ Tree_to_frac(tree);
        //@ Tree_split_frac(tree);
        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        
        let product = join(product_join_handle);
        
        //@ Tree_merge_frac(tree);
        //@ Tree_frac_to_full(tree);
        Tree::dispose(tree);
        
        print_u64(sum);
        print_u64(product);
    }
}