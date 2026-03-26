/*@ pred tree(*mut Tree t; i32 v) =
    t == null ? emp :
    alloc_block_t(t, std::alloc::Layout::new::<Tree>()) &*&
    struct_Tree_padding(t) &*&
    (*t).value |-> ?val &*&
    (*t).left |-> ?l &*& (*t).right |-> ?r &*&
    tree(l, _) &*& tree(r, _) &*&
    v == val;
@*/

/*@ pred fold_data(*mut FoldData d; *mut Tree t, FoldFunction f, i32 acc) =
    d == null ? emp :
    alloc_block_t(d, std::alloc::Layout::new::<FoldData>()) &*&
    struct_FoldData_padding(d) &*&
    (*d).tree |-> t &*& (*d).f |-> f &*& (*d).acc |-> acc &*&
    thread((*d).thread, folder, d);
@*/

use std::alloc::{Layout, alloc, dealloc, handle_alloc_error};

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
    //@ ens tree(result, _);
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
            //@ close alloc_block_t(t, Layout::new::<Tree>());
            //@ close struct_Tree_padding(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t, value);
            t
        }
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req tree(tree, _);
    //@ ens emp;
    {
        if !tree.is_null() {
            //@ open tree(tree, _);
            //@ open alloc_block_t(tree, _);
            //@ open struct_Tree_padding(tree);
            let l = (*tree).left;
            let r = (*tree).right;
            Self::dispose(l);
            Self::dispose(r);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req tree(tree, _) &*& [_]is_FoldFunction(f);
    //@ ens tree(tree, _) &*& [_]is_FoldFunction(f);
    {
        if tree.is_null() {
            acc
        } else {
            //@ open tree(tree, _);
            let l = (*tree).left;
            let r = (*tree).right;
            let v = (*tree).value;
            //@ close tree(tree, v);
            acc = Self::fold(l, f, acc);
            acc = Self::fold(r, f, acc);
            acc = f(acc, v);
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
//@ req fold_data(data, ?t, ?f, ?a0) &*& tree(t, _);
//@ ens fold_data(data, t, f, ?a1) &*& tree(t, _) &*& a1 == Tree::fold(t, f, a0);
{
    
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req tree(tree, _) &*& [_]is_FoldFunction(f);
//@ ens fold_data(result, tree, f, acc) &*& tree(tree, _);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    //@ close alloc_block_t(data, Layout::new::<FoldData>());
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
//@ req fold_data(data, ?t, ?f, ?a0) &*& tree(t, _);
//@ ens tree(t, _) &*& result == Tree::fold(t, f, a0);
{
    platform::threading::join((*data).thread);
    
    let result = (*data).acc;
    //@ open fold_data(data, _, _, _);
    //@ open alloc_block_t(data, _);
    //@ open struct_FoldData_padding(data);
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