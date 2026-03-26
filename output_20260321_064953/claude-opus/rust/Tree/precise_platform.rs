use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Tree(t: *mut Tree; depth: i32) =
    if t == 0 {
        true
    } else {
        (*t).left |-> ?left &*& (*t).right |-> ?right &*& (*t).value |-> ?v &*&
        struct_Tree_padding(t) &*&
        Tree(left, depth - 1) &*& Tree(right, depth - 1) &*&
        alloc_block(t as *mut u8, Layout::new_::<Tree>())
    };

pred FoldData_own(d: *mut FoldData;) =
    (*d).thread |-> ?th &*& (*d).tree |-> ?tr &*& (*d).f |-> ?f &*& (*d).acc |-> ?acc &*&
    struct_FoldData_padding(d) &*&
    alloc_block(d as *mut u8, Layout::new_::<FoldData>());
@*/

unsafe fn random_int(max: i32) -> i32
//@ req true;
//@ ens true;
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
//@ req x >= 1;
//@ ens true;
{
    let mut result = 1;
    loop {
        //@ inv x >= 1;
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
    //@ ens Tree(result, depth);
    {
        if depth == 0 {
            //@ close Tree(std::ptr::null_mut(), 0);
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
            //@ close Tree(t, depth);
            t
        }
    }

    unsafe fn dispose(tree: *mut Tree)
    //@ req Tree(tree, ?depth);
    //@ ens true;
    {
        //@ open Tree(tree, depth);
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    //@ req Tree(tree, ?depth);
    //@ ens Tree(tree, depth);
    {
        //@ open Tree(tree, depth);
        if tree.is_null() {
            //@ close Tree(tree, depth);
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            //@ close Tree(tree, depth);
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
//@ req true;
//@ ens true;
{
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
//@ req true;
//@ ens true;
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
//@ req true;
//@ ens true;
{
    platform::threading::join((*data).thread);
    
    let result = (*data).acc;
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