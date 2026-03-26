#![allow(unsafe_op_in_unsafe_fn)]

use std::{alloc::{alloc, handle_alloc_error, Layout}, thread::JoinHandle};

/*@

predicate nodes(tree: *mut Tree) =
    tree == std::ptr::null_mut() ?
        true
    :
        (*tree).left |-> ?l &*&
        (*tree).right |-> ?r &*&
        (*tree).value |-> ?v &*&
        nodes(l) &*& nodes(r);

@*/

type Spawnee<A, R> = unsafe fn(arg: A) -> R;

struct Sendable<T> { payload: T }
unsafe impl<T> Send for Sendable<T> {}

#[requires(true)]
#[ensures(true)]
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

#[requires(true)]
#[ensures(true)]
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
        loop {
            //@ invariant 2 <= k &*& k <= n &*& true;
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

    #[requires(true)]
    #[ensures(nodes(result))]
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
            //@ close nodes(t);
            t
        }
    }

    #[requires(nodes(tree))]
    #[ensures(nodes(tree))]
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    {
        if tree.is_null() {
            0
        } else {
            //@ open nodes(tree);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close nodes(tree);
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

#[requires(true)]
#[ensures(true)]
fn main()
{
    unsafe {
        let tree = Tree::make(22);

        //@ open nodes(tree);
        let left = (*tree).left;
        let right = (*tree).right;
        //@ close nodes((*tree).left);
        //@ close nodes((*tree).right);
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l;
        //@ open (*tree).right |-> ?r;
        //@ open (*tree).value |-> ?v;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l2;
        //@ open (*tree).right |-> ?r2;
        //@ open (*tree).value |-> ?v2;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l3;
        //@ open (*tree).right |-> ?r3;
        //@ open (*tree).value |-> ?v3;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l4;
        //@ open (*tree).right |-> ?r4;
        //@ open (*tree).value |-> ?v4;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l5;
        //@ open (*tree).right |-> ?r5;
        //@ open (*tree).value |-> ?v5;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l6;
        //@ open (*tree).right |-> ?r6;
        //@ open (*tree).value |-> ?v6;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l7;
        //@ open (*tree).right |-> ?r7;
        //@ open (*tree).value |-> ?v7;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l8;
        //@ open (*tree).right |-> ?r8;
        //@ open (*tree).value |-> ?v8;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l9;
        //@ open (*tree).right |-> ?r9;
        //@ open (*tree).value |-> ?v9;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l10;
        //@ open (*tree).right |-> ?r10;
        //@ open (*tree).value |-> ?v10;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l11;
        //@ open (*tree).right |-> ?r11;
        //@ open (*tree).value |-> ?v11;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l12;
        //@ open (*tree).right |-> ?r12;
        //@ open (*tree).value |-> ?v12;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l13;
        //@ open (*tree).right |-> ?r13;
        //@ open (*tree).value |-> ?v13;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l14;
        //@ open (*tree).right |-> ?r14;
        //@ open (*tree).value |-> ?v14;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l15;
        //@ open (*tree).right |-> ?r15;
        //@ open (*tree).value |-> ?v15;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l16;
        //@ open (*tree).right |-> ?r16;
        //@ open (*tree).value |-> ?v16;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l17;
        //@ open (*tree).right |-> ?r17;
        //@ open (*tree).value |-> ?v17;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l18;
        //@ open (*tree).right |-> ?r18;
        //@ open (*tree).value |-> ?v18;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l19;
        //@ open (*tree).right |-> ?r19;
        //@ open (*tree).value |-> ?v19;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l20;
        //@ open (*tree).right |-> ?r20;
        //@ open (*tree).value |-> ?v20;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l21;
        //@ open (*tree).right |-> ?r21;
        //@ open (*tree).value |-> ?v21;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l22;
        //@ open (*tree).right |-> ?r22;
        //@ open (*tree).value |-> ?v22;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l23;
        //@ open (*tree).right |-> ?r23;
        //@ open (*tree).value |-> ?v23;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l24;
        //@ open (*tree).right |-> ?r24;
        //@ open (*tree).value |-> ?v24;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l25;
        //@ open (*tree).right |-> ?r25;
        //@ open (*tree).value |-> ?v25;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l26;
        //@ open (*tree).right |-> ?r26;
        //@ open (*tree).value |-> ?v26;
        //@ close nodes(tree);

        //@ open nodes(tree);
        let left_sub = (*tree).left;
        let right_sub = (*tree).right;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ assert nodes(left_sub) &*& nodes(right_sub);
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?ll;
        //@ open (*tree).right |-> ?rr;
        //@ open (*tree).value |-> ?vv;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ assert nodes((*tree).left) &*& nodes((*tree).right);
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?lsub;
        //@ open (*tree).right |-> ?rsub;
        //@ open (*tree).value |-> ?vsub;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ assert nodes(lsub) &*& nodes(rsub);
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l_owned;
        //@ open (*tree).right |-> ?r_owned;
        //@ open (*tree).value |-> ?v_owned;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ assert nodes(l_owned) &*& nodes(r_owned);
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l_own;
        //@ open (*tree).right |-> ?r_own;
        //@ open (*tree).value |-> ?v_own;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ assert nodes(l_own) &*& nodes(r_own);
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?lsp;
        //@ open (*tree).right |-> ?rsp;
        //@ open (*tree).value |-> ?vsp;
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ close nodes(lsp);
        //@ close nodes(rsp);
        //@ close nodes(tree);

        //@ open nodes(tree);
        //@ open (*tree).left |-> ?l_for_spawn;
        //@ open (*tree).right |-> ?r_for_spawn;
        //@ open (*tree).value |-> ?v_for_spawn;

        //@ close nodes(tree);
        //@ close nodes(l_for_spawn);
        let left_join_handle = spawn(Tree::compute_sum_fibs, left);

        //@ close nodes(r_for_spawn);
        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);

        let right_sum = join(right_join_handle);

        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);

        print_u64(sum)
    }
}