#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

predicate tree(*mut Tree t; u8 depth) =
    match depth {
        0 => t == std::ptr::null_mut(),
        _ => exists(u8 d1, u8 d2)
             &*& *t |-> ?left &*& *t[1] |-> ?right &*& *t[2] |-> ?value
             &*& value == 5000
             &*& tree(left, d1) &*& tree(right, d2)
             &*& d1 + 1 <= depth &*& d2 + 1 <= depth,
    };

predicate join_handle<Sendable<R>>(JoinHandle<Sendable<R>> h; predicate() P, R result) =
    [_]h.join_handle(h, P, result);

lemma void tree_split(*mut Tree t, u8 depth)
    requires tree(t, depth) &*& depth > 0;
    ensures
        exists(*mut Tree left, *mut Tree right)
        &*& *t |-> left &*& *t[1] |-> right &*& *t[2] |-> 5000
        &*& tree(left, ?d1) &*& tree(right, ?d2)
        &*& d1 + 1 <= depth &*& d2 + 1 <= depth;
{
    open tree(t, depth);
    assert exists(_, _);
    let (left, right) = (?l, ?r);
    close tree_split(t, depth);
}

lemma void tree_join(*mut Tree t, *mut Tree left, *mut Tree right, u8 d1, u8 d2)
    requires
        *t |-> left &*& *t[1] |-> right &*& *t[2] |-> 5000
        &*& tree(left, d1) &*& tree(right, d2);
    ensures tree(t, max(d1, d2) + 1);
{
    close tree(t, max(d1, d2) + 1);
}

#[requires(depth == 0 ==> emp)]
#[ensures(match depth { 0 => result == std::ptr::null_mut(), _ => tree(result, depth) })]
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

#[requires(tree(tree, ?depth))]
#[ensures(tree(tree, depth))]
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

#[requires(predicate() P &*& P())]
#[ensures(join_handle(result, P, ?r) &*& P())]
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

#[requires(join_handle(h, ?P, ?r))]
#[ensures(P() &*& result == r)]
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    h.join().unwrap().payload
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