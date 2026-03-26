//@ req true;
//@ ens true;
use std::alloc::{Layout, alloc, handle_alloc_error};

/*@ pred tree(?t, ?v) =
    t == null ?
        v == 0
    :
        alloc_block(t, std::alloc::Layout::new::<Tree>()) &*&
        struct_Tree_padding(t) &*&
        (*t).value |-> ?val &*&
        tree((*t).left, ?vl) &*&
        tree((*t).right, ?vr) &*&
        v == vl + vr + 1;
@*/

/*@ pred fold_data(?d, ?tree, ?f, ?acc) =
    d != null ?
        alloc_block(d, std::alloc::Layout::new::<FoldData>()) &*&
        struct_FoldData_padding(d) &*&
        (*d).tree |-> tree &*&
        (*d).f |-> f &*&
        (*d).acc |-> acc
    :
        false;
@*/

unsafe fn random_int(max: i32) -> i32
//@ req true;
//@ ens true;
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
//@ req true;
//@ ens true;
{
    let mut result = 1;
    loop {
        //@ inv true;
        if x == 1 {
            return result;
        }
        result *= x;
        x -= 1;
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: i32,
}

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {

    unsafe fn make(depth: i32) -> *mut Tree
    //@ req true;
    //@ ens tree(result, ?v);
    {
        if depth == 0 {
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = random_int(5);
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ close tree(left, _);
            //@ close tree(right, _);
            //@ close struct_Tree_padding(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t, _);
            t
        }
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req tree(tree, _);
    //@ ens true;
    {
        if !tree.is_null() {
            //@ open tree(tree, _);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req tree(tree, ?size);
    //@ ens true;
    {
        if tree.is_null() {
            acc
        } else {
            //@ open tree(tree, _);
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close tree(tree, size);
            acc
        }
    }

}

struct FoldData {
    thread: platform::threading::Thread,
    tree: *mut Tree,
    f: FoldFunction,
    acc: i32,
}

unsafe fn folder(data: *mut FoldData)
//@ req fold_data(data, ?tree, ?f, ?acc_init) &*& tree(tree, _);
//@ ens fold_data(data, tree, f, ?acc_final);
{
    
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req tree(tree, _) &*& true; // assume fork_joinable handles concurrency
//@ ens fold_data(result, tree, f, acc);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    //@ close struct_FoldData_padding(data);
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    //@ close fold_data(data, tree, f, acc);
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req fold_data(data, ?tree, ?f, ?acc);
//@ ens true;
{
    platform::threading::join((*data).thread);
    
    let result = (*data).acc;
    //@ open fold_data(data, _, _, _);
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

unsafe fn sum_function(acc: i32, x: i32) -> i32
//@ req true;
//@ ens true;
{
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32
//@ req true;
//@ ens true;
{
    acc ^ fac(x)
}

unsafe fn print_i32(value: i32)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}

fn main() {
    unsafe {
        let tree = Tree::make(21);
        
        let sum_data = start_fold_thread(tree, sum_function, 0);
        
        let xor_data = start_fold_thread(tree, xor_function, 0);
        let sum = join_fold_thread(sum_data);
        let xor = join_fold_thread(xor_data);
        Tree::dispose(tree);
        print_i32(sum - xor);
    }
}