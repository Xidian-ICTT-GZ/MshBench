#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

predicate tree(tree_ptr: *mut Tree; u64) = 
    tree_ptr != std::ptr::null_mut() ?
        exists (left_ptr: *mut Tree, right_ptr: *mut Tree, value: u16, left_sum: u64, right_sum: u64) &*&
            tree_ptr->Tree { left: left_ptr, right: right_ptr, value: value } &*&
            tree(left_ptr, left_sum) &*& tree(right_ptr, right_sum) &*&
            wrapping_fib_spec(value, wrapping_fib(value)) &*&
            wrapping_add_spec(left_sum, wrapping_fib(value), right_sum, _)
        :
        tree_ptr == std::ptr::null_mut() &*& emp;

predicate wrapping_fib_spec(u16 v; u64 result) = true;
    

predicate wrapping_add_spec(u64 left, u64 mid, u64 right, u64? res) = true;
    

impl Tree {

    #[requires(depth >= 0)]
    #[ensures(tree(result, ?sum))]
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
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            t
        }
    }

    #[requires(tree(tree, ?sum_in))]
    #[ensures(tree(tree, sum_in) &*& result == sum_in)]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    {
        if tree.is_null() {
            0
        } else {
            
            
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

}

#[requires(true)]
#[ensures(result == wrapping_fib_spec(n))]
unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            
            #[invariant(k <= n &*& fib_k_minus_1 != 0 &*& fib_k != 0)]
            if k == n { break; }
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

#[requires(true)]
#[ensures(true)]
unsafe fn print_u64(value: u64)
{
    println!("{}", value);
}

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    h.join().unwrap().payload
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        
        let left = (*tree).left;
        let right = (*tree).right;
        
        let left_join_handle = spawn(Tree::compute_sum_fibs, left);
        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);
        let right_sum = join(right_join_handle);

        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);
        print_u64(sum)
    }
}

  

impl Tree {
    #[predicate]
    fn Tree(&self) -> bool
    {
        true
    }
}

#[predicate]
fn tree_struct(t: *mut Tree; left: *mut Tree, right: *mut Tree, value: u16) = 
    t->Tree { left: left, right: right, value: value };

#[predicate]
fn tree(t: *mut Tree, sum: u64) = 
    t == std::ptr::null_mut() ? emp : 
    exists<*mut Tree, *mut Tree, u16, u64, u64>(|left, right, value, left_sum, right_sum| 
        t->Tree { left: left, right: right, value: value } &*&
        tree(left, left_sum) &*&
        tree(right, right_sum) &*&
        wrapping_fib_spec(value, wrapping_fib(value)) &*&
        wrapping_add_spec(left_sum, wrapping_fib(value), right_sum, sum)
    );