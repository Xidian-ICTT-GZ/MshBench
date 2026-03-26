#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

/*@

predicate sendable<T>(v: T) = true;

@*/

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
/*@
requires true;
ensures true;
@*/
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
/*@
requires true;
ensures true;
@*/
{
    h.join().unwrap().payload
}

unsafe fn wrapping_fib(n: u16) -> u64
/*@
requires true;
ensures true;
@*/
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            /*@
            invariant 2 <= k &*& k <= n &*& true;
            @*/
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

/*@

predicate tree_nodes(struct Tree *t; int depth) =
    t == 0 ?
        depth == 0
    :
        depth > 0 &*&
        struct_Tree_left(t, ?l) &*&
        struct_Tree_right(t, ?r) &*&
        struct_Tree_value(t, ?v) &*&
        tree_nodes(l, depth - 1) &*&
        tree_nodes(r, depth - 1);

@*/

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    /*@
    requires true;
    ensures tree_nodes(result, depth as int);
    @*/
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

            //@ close struct_Tree_left(t, left);
            //@ close struct_Tree_right(t, right);
            //@ close struct_Tree_value(t, value);
            //@ close tree_nodes(left, depth as int - 1);
            //@ close tree_nodes(right, depth as int - 1);
            //@ close tree_nodes(t, depth as int);

            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    /*@
    requires tree_nodes(tree, ?d);
    ensures tree_nodes(tree, d);
    @*/
    {
        if tree.is_null() {
            //@ open tree_nodes(tree, d);
            0
        } else {
            //@ open tree_nodes(tree, d);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree_nodes((*tree).left, d - 1);
            //@ close tree_nodes((*tree).right, d - 1);
            //@ close tree_nodes(tree, d);

            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    /*@
    requires tree_nodes(tree, ?d);
    ensures tree_nodes(tree, d);
    @*/
    {
        if tree.is_null() {
            //@ open tree_nodes(tree, d);
            1
        } else {
            //@ open tree_nodes(tree, d);
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close tree_nodes((*tree).left, d - 1);
            //@ close tree_nodes((*tree).right, d - 1);
            //@ close tree_nodes(tree, d);

            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }

}

unsafe fn print_u64(value: u64)
/*@
requires true;
ensures true;
@*/
{
    println!("{}", value);
}

fn main()
/*@
requires true;
ensures true;
@*/
{
    unsafe {
        let tree = Tree::make(22);

        //@ open tree_nodes(tree, 22);
        //@ close tree_nodes(tree, 22);
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);

        //@ open tree_nodes(tree, 22);
        //@ close tree_nodes(tree, 22);
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);

        let sum = join(sum_join_handle);

        let product = join(product_join_handle);

        print_u64(sum);
        print_u64(product);
    }
}