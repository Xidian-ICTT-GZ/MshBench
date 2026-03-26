use std::alloc::{Layout, alloc, handle_alloc_error};

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

/*@
pred tree(t: *mut Tree) =
    t == std::ptr::null_mut() ?
        true
    :
        (*t).left |-> ?l &*&
        (*t).right |-> ?r &*&
        (*t).value |-> ?v &*&
        tree(l) &*& tree(r);

pred fold_data(d: *mut FoldData) =
    (*d).thread |-> ?thr &*&
    (*d).tree |-> ?t &*&
    (*d).f |-> ?f &*&
    (*d).acc |-> ?acc;
@*/

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {

    unsafe fn make(depth: i32) -> *mut Tree
    //@ req true;
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
            std::alloc::dealloc(tree as *mut u8, Layout::new::<Tree>());
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
//@ req fold_data(data);
//@ ens fold_data(data);
{
    //@ open fold_data(data);
    
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    
    //@ close fold_data(data);
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req true;
//@ ens fold_data(result);
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    
    

    //@ close fold_data(data);
    let t = platform::threading::fork_joinable(folder, data);
    //@ open fold_data(data);
    (*data).thread = t;
    //@ close fold_data(data);
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req fold_data(data);
//@ ens true;
{
    //@ open fold_data(data);
    platform::threading::join((*data).thread);
    
    let result = (*data).acc;
    std::alloc::dealloc(data as *mut u8, Layout::new::<FoldData>());
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