use std::alloc::{Layout, alloc, handle_alloc_error};

//@ ghost predicate tree_valid(t: *mut Tree) = match t {
//@     null => true,
//@     non_null => tree_node_valid(t) &* tree_valid((*t).left) &* tree_valid((*t).right),
//@ };
//@
//@ predicate tree_node_valid(t: *mut Tree) = exists(i32 left_val, i32 right_val, i32 val;
//@     int_field::<Tree>(t, "left", left_val) &*
//@     int_field::<Tree>(t, "right", right_val) &*
//@     int_field::<Tree>(t, "value", val) &*
//@     tree_valid(left_val as *mut Tree) &*
//@     tree_valid(right_val as *mut Tree)
//@ );

unsafe fn random_int(max: i32) -> i32
{
    max - 1 
}

//@ req true;
//@ ens true;
unsafe fn fac(mut x: i32) -> i32
{
    let mut result = 1;
    loop {
        
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

    //@ req depth >= 0;
    //@ ens tree_valid(result);
    unsafe fn make(depth: i32) -> *mut Tree
    
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

    //@ req tree_valid(tree);
    //@ ens tree_valid(null);
    unsafe fn dispose(tree: *mut Tree)
    
    {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    //@ req tree_valid(tree);
    //@ ens true;
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    
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
    thread: *mut u8,
    tree: *mut Tree,
    f: FoldFunction,
    acc: i32,
}

//@ ghost predicate folddata_valid(d: *mut FoldData) = exists(*mut Tree t, FoldFunction func, i32 a;
//@     int_field::<FoldData>(d, "thread", _) &*
//@     int_field::<FoldData>(d, "tree", (t as i64)) &*
//@     int_field::<FoldData>(d, "f", (func as i64)) &*
//@     int_field::<FoldData>(d, "acc", a) &*
//@     tree_valid(t)
//@ );

unsafe fn folder(data: *mut FoldData)
{
    
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    
}

//@ req tree_valid(tree);
//@ ens folddata_valid(result);
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
{
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;
    
    

    let t = std::ptr::null_mut();
    (*data).thread = t;
    data
}

//@ req folddata_valid(data);
//@ ens true;
unsafe fn join_fold_thread(data: *mut FoldData) -> i32
{
    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

unsafe fn sum_function(acc: i32, x: i32) -> i32
{
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32
{
    acc ^ fac(x)
}

unsafe fn print_i32(value: i32)
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