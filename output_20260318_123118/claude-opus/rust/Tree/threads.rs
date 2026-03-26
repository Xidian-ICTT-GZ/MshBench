#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

predicate tree(struct Tree* tree_ptr, int depth) =
    depth > 0 ?
        tree_ptr |-> {left: ?l, right: ?r, value: ?v} &*&
        tree(l, depth - 1) &*&
        tree(r, depth - 1)
    :
    tree_ptr == 0;

predicate sendable<R>(Sendable<R>* ptr; R payload) =
    ptr |-> Sendable { payload: payload };

#[requires(sendable(arg_ptr, arg_payload))]
#[ensures(sendable(?result_ptr, ?res_payload) &*& res_payload == f_payload)]
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static

{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

#[requires(sendable(ptr, r))]
#[ensures(result == r)]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R

{
    h.join().unwrap().payload
}

#[requires(true)]
#[ensures(true)]
unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop
            #[invariant(k <= n &*& 
                        fib_k_minus_1 == wrapping_fib(k - 1) &*& 
                        fib_k == wrapping_fib(k))]
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

    #[requires(depth >= 0)]
    #[ensures(tree(result, depth))]
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

    #[requires(tree(tree, ?d))]
    #[ensures(tree(tree, d) &*& result == 
        (tree == 0 ? 0 : (Self::compute_sum_fibs((*tree).left) 
                         .wrapping_add(wrapping_fib((*tree).value))
                         .wrapping_add(Self::compute_sum_fibs((*tree).right)))))]
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
#[ensures(true)]
unsafe fn print_u64(value: u64)
{
    println!("{}", value);
}

fn main()
{
    unsafe {
        let tree = Tree::make(22);
        assume(tree != std::ptr::null_mut()); 
        let left = (*tree).left;
        let right = (*tree).right;

        #[predicate] 
        fn sendable<T>(Sendable<T>* ptr, T payload);

        #[requires(tree(tree, 22))]
        #[ensures(true)]
        {
            let left_join_handle = spawn(Tree::compute_sum_fibs, left);
            let right_join_handle = spawn(Tree::compute_sum_fibs, right);
            let root_fib = wrapping_fib((*tree).value);

            let left_sum = join(left_join_handle);
            let right_sum = join(right_join_handle);

            let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);

            print_u64(sum);
        }
    }
}