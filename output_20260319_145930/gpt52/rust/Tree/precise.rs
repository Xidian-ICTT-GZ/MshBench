#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout, dealloc}, thread::JoinHandle};

/*@

pred tree_nodes(*mut Tree tree) =
    tree == 0 ?
        true
    :
        alloc_block_tree(tree) &*&
        (*tree).left |-> ?l &*&
        (*tree).right |-> ?r &*&
        (*tree).value |-> ?v &*&
        tree_nodes(l) &*& tree_nodes(r);

@*/

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

    //@ req true;
    //@ ens tree_nodes(result);
    unsafe fn make(depth: u8) -> *mut Tree
    {
        if depth == 0 {
            //@ close tree_nodes(0);
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
            //@ close tree_nodes(t);
            t
        }
    }

    //@ req tree_nodes(tree);
    //@ ens tree_nodes(tree);
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    {
        //@ open tree_nodes(tree);
        if tree.is_null() {
            //@ close tree_nodes(0);
            0
        } else {
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree_nodes(tree);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }
    
    //@ req tree_nodes(tree);
    //@ ens tree_nodes(tree);
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    {
        //@ open tree_nodes(tree);
        if tree.is_null() {
            //@ close tree_nodes(0);
            1
        } else {
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close tree_nodes(tree);
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
    
    //@ req tree_nodes(tree);
    //@ ens true;
    unsafe fn dispose(tree: *mut Tree)
    {
        //@ open tree_nodes(tree);
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            //@ open alloc_block_tree(tree);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        } else {
            //@ close tree_nodes(0);
        }
    }

}

//@ req true;
//@ ens true;
//@ assume_correct
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
        
        Tree::dispose(tree);
        
        print_u64(sum);
        print_u64(product);
    }
}