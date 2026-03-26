use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate Tree_own(t: *mut Tree) =
  t != core::ptr::null_mut::<Tree>() ==>
    (t as usize) % core::mem::align_of::<Tree>() == 0 &&
    Tree_own((*t).left) * Tree_own((*t).right) * integer((*t).value);

predicate FoldData_own(d: *mut FoldData) =
  d != core::ptr::null_mut::<FoldData>() ==>
    (d as usize) % core::mem::align_of::<FoldData>() == 0 &&
    Tree_own((*d).tree) * integer((*d).acc);

unsafe fn random_int(max: i32) -> i32 {
    max - 1
}

#[requires(x >= 1)]
#[ensures(result >= 1)]
unsafe fn fac(mut x: i32) -> i32 {
    let mut result = 1;
    loop {
        #[invariant(x >= 1 && result >= 1)]
        {
            if x == 1 {
                return result;
            }
            result *= x;
            x -= 1;
        }
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: i32,
}

type FoldFunction = unsafe fn(acc: i32, x: i32) -> i32;

impl Tree {
    #[requires(depth >= 0)]
    #[ensures(result == core::ptr::null_mut::<Tree>() ==> emp &*& result != core::ptr::null_mut::<Tree>() ==> Tree_own(result))]
    unsafe fn make(depth: i32) -> *mut Tree {
        if depth == 0 {
            core::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = random_int(5);
            let layout = Layout::new::<Tree>();
            let t = alloc(layout) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(layout);
            }
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            t
        }
    }

    #[requires(tree == core::ptr::null_mut::<Tree>() ==> emp &*& tree != core::ptr::null_mut::<Tree>() ==> Tree_own(tree))]
    #[ensures(emp)]
    unsafe fn dispose(tree: *mut Tree) {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    #[requires(tree == core::ptr::null_mut::<Tree>() ==> emp &*& tree != core::ptr::null_mut::<Tree>() ==> Tree_own(tree))]
    #[ensures(emp)]
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32 {
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
    thread: std::thread::JoinHandle<()>,
    tree: *mut Tree,
    f: FoldFunction,
    acc: i32,
}

#[requires(FoldData_own(data))]
#[ensures(emp)]
unsafe fn folder(data: *mut FoldData) {
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

#[requires(tree == core::ptr::null_mut::<Tree>() ==> emp &*& tree != core::ptr::null_mut::<Tree>() ==> Tree_own(tree))]
#[ensures(FoldData_own(result))]
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData {
    let layout = Layout::new::<FoldData>();
    let data = alloc(layout) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(layout);
    }
    (*data).tree = tree;
    (*data).f = f;
    (*data).acc = acc;

    let t = std::thread::spawn(move || {
        folder(data);
    });
    (*data).thread = t;
    data
}

#[requires(FoldData_own(data))]
#[ensures(emp)]
unsafe fn join_fold_thread(data: *mut FoldData) -> i32 {
    let _ = (*data).thread.join();

    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

#[requires(true)]
#[ensures(true)]
unsafe fn sum_function(acc: i32, x: i32) -> i32 {
    acc + fac(x)
}

#[requires(true)]
#[ensures(true)]
unsafe fn xor_function(acc: i32, x: i32) -> i32 {
    acc ^ fac(x)
}

unsafe fn print_i32(value: i32) {
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