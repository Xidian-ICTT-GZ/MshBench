use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

pred Tree_(t: *mut Tree) =
    if t == std::ptr::null_mut() {
        emp
    } else {
        (*t).left |-> ?l &*& (*t).right |-> ?r &*& (*t).value |-> ?v &*& Tree_(l) &*& Tree_(r)
    };

pred FoldData_(d: *mut FoldData) =
    (*d).thread |-> ?th &*& (*d).tree |-> ?tr &*& (*d).f |-> ?f &*& (*d).acc |-> ?acc &*& Tree_(tr);

pred FoldJob(d: *mut FoldData) =
    (*d).tree |-> ?tr &*& (*d).f |-> ?f &*& (*d).acc |-> ?acc &*& Tree_(tr);

use std::alloc::{Layout as Layout2, alloc as alloc2, handle_alloc_error as handle_alloc_error2};

unsafe fn random_int(max: i32) -> i32
    #[requires(true)]
    #[ensures(true)]
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
    #[requires(x >= 1)]
    #[ensures(true)]
{
    let mut result = 1;
    loop {
        #[invariant(x >= 1)]
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
        #[requires(depth >= 0)]
        #[ensures(Tree_(result))]
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
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            t
        }
    }

    unsafe fn dispose(tree: *mut Tree)
        #[requires(Tree_(tree))]
        #[ensures(emp)]
    {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
        #[requires(Tree_(tree))]
        #[ensures(Tree_(tree))]
    {
        if tree.is_null() {
            acc
        } else {
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
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
    #[requires(FoldJob(data))]
    #[ensures(FoldData_(data))]
{
    
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
    #[requires(Tree_(tree))]
    #[ensures(FoldData_(result))]
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    
    

    //@ open FoldData_(data); // cannot; not established yet
    //@ close FoldJob(data);
    let t = platform::threading::fork_joinable(folder, data);
    (*data).thread = t;
    //@ close FoldData_(data);
    data
}

unsafe fn join_fold_thread(data: *mut FoldData) -> i32
    #[requires(FoldData_(data))]
    #[ensures(Tree_((*data).tree))]
{
    //@ open FoldData_(data);
    platform::threading::join((*data).thread);
    
    let result = (*data).acc;
    //@ open Tree_((*data).tree);
    //@ close Tree_((*data).tree);
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

unsafe fn sum_function(acc: i32, x: i32) -> i32
    #[requires(x >= 1)]
    #[ensures(true)]
{
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32
    #[requires(x >= 1)]
    #[ensures(true)]
{
    acc ^ fac(x)
}

unsafe fn print_i32(value: i32)
    #[requires(true)]
    #[ensures(true)]
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