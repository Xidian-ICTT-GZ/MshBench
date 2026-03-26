use std::alloc::{Layout, alloc, handle_alloc_error};
//@ use std::alloc::Layout;

//@ pred tree(t: *mut Tree) =
//@     if t == std::ptr::null_mut() {
//@         true
//@     } else {
//@         (*t).left |-> ?l &*& (*t).right |-> ?r &*& (*t).value |-> ?v &*& std::alloc::alloc_block(t as *mut u8, Layout::new::<Tree>()) &*& tree(l) &*& tree(r)
//@     };
//@
//@ pred folddata(d: *mut FoldData) =
//@     (*d).thread |-> ?th &*& (*d).tree |-> ?tr &*& (*d).f |-> ?f &*& (*d).acc |-> ?acc &*& std::alloc::alloc_block(d as *mut u8, Layout::new::<FoldData>());
//@

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
    //@ req depth >= 0;
    //@ ens tree(result);
    {
        if depth == 0 {
            //@ close tree(std::ptr::null_mut());
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = random_int(5);
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            //@ close std::alloc::alloc_block(t as *mut u8, Layout::new::<Tree>());
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t);
            t
        }
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req tree(tree);
    //@ ens true;
    {
        //@ open tree(tree);
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            //@ open std::alloc::alloc_block(tree as *mut u8, Layout::new::<Tree>());
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req tree(tree);
    //@ ens tree(tree);
    {
        //@ open tree(tree);
        if tree.is_null() {
            //@ close tree(tree);
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close tree(tree);
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
    //@ req folddata(data) &*& tree((*data).tree);
    //@ ens folddata(data) &*& tree((*data).tree);
{
    //@ open folddata(data);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    //@ close folddata(data);
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req tree(tree);
//@ ens folddata(result) &*& tree(tree);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    //@ close std::alloc::alloc_block(data as *mut u8, Layout::new::<FoldData>());
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;

    //@ close folddata(data);
    //@ open folddata(data);
    //@ close folddata(data);
    let t = platform::threading::fork_joinable(folder, data);
    //@ open folddata(data);
    (*data).thread = t;
    //@ close folddata(data);
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req folddata(data) &*& tree((*data).tree);
//@ ens tree((*data).tree);
{
    //@ open folddata(data);
    platform::threading::join((*data).thread);
    //@ close folddata(data);
    //@ open folddata(data);
    let result = (*data).acc;
    //@ open std::alloc::alloc_block(data as *mut u8, Layout::new::<FoldData>());
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