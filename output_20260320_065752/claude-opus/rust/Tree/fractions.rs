#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

/*@ pred tree(tree_ptr: *mut Tree) {
    // Recursive tree predicate: either null or valid allocated Tree struct with subtree predicates
    (tree_ptr == 0) 
    || (alloc_block_tree(tree_ptr) &*&
        tree_ptr->left |-> ?left_ptr &*&
        tree_ptr->right |-> ?right_ptr &*&
        tree_ptr->value |-> _ &*&
        tree(left_ptr) &*& tree(right_ptr))
}

predicate alloc_block_tree(Tree* p;) = alloc_block(p, sizeof(Tree)); 
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
//@ ensures true;
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    h.join().unwrap().payload
}

//@ req true;
//@ ensures true;
unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        //@ inv k <= n + 1 &*& true; // simple loop invariant for safety
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

    //@ req true;
    //@ ensures tree(result);
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
            //@ close tree(left);
            //@ close tree(right);
            //@ close alloc_block_tree(t as *mut Tree);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t);
            t
        }
    }

    //@ req tree(tree);
    //@ ensures true;
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    {
        if tree.is_null() {
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
    
    //@ req tree(tree);
    //@ ensures true;
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    {
        if tree.is_null() {
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
    
}

//@ req true;
//@ ensures true;
unsafe fn print_u64(value: u64)
{
    println!("{}", value);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        //@ close tree(tree);
        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        let product = join(product_join_handle);
        
        print_u64(sum);
        print_u64(product);
        //@ open tree(tree);
        
    }
}