use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn tree_points_to(t: *mut Tree, left: *mut Tree, right: *mut Tree, value: i32) -> bool {
    true
}

#[predicate]
fn tree_full(t: *mut Tree) -> bool {
    !t.is_null() && exists!(left: *mut Tree, right: *mut Tree, value: i32 |
        tree_points_to(t, left, right, value) &&
        tree_full(left) && tree_full(right)
    )
}

#[predicate]
fn tree_fraction(t: *mut Tree, p: Perm) -> bool {
    !t.is_null() && exists!(left: *mut Tree, right: *mut Tree, value: i32 |
        tree_points_to(t, left, right, value) @ p &&
        tree_fraction(left, p) && tree_fraction(right, p)
    )
}

#[predicate]
fn fold_data_points_to(d: *mut FoldData, tree: *mut Tree, f: FoldFunction, acc: i32) -> bool {
    true
}

#[predicate]
fn fold_data_full(d: *mut FoldData) -> bool {
    !d.is_null() && exists!(tree: *mut Tree, f: FoldFunction, acc: i32 |
        fold_data_points_to(d, tree, f, acc)
    )
}

unsafe fn random_int(max: i32) -> i32 {
    #[requires(max > 0)]
    #[ensures(result >= 0 && result < max)]
    max - 1
}

unsafe fn fac(mut x: i32) -> i32 {
    #[requires(x >= 0)]
    #[ensures(result >= 1)]
    let mut result = 1;
    #[invariant(x >= 0)]
    #[invariant(result >= 1)]
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
    unsafe fn make(depth: i32) -> *mut Tree {
        #[requires(depth >= 0)]
        #[ensures(tree_full(result))]
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

    unsafe fn dispose(tree: *mut Tree) {
        #[requires(tree_full(tree))]
        #[ensures(true)]
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32 {
        #[requires(tree_fraction(tree, 1/2))]
        #[ensures(tree_fraction(tree, 1/2))]
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

unsafe fn folder(data: *mut FoldData) {
    #[requires(fold_data_full(data))]
    #[ensures(true)]
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData {
    #[requires(tree_fraction(tree, 1/2))]
    #[ensures(fold_data_full(result))]
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

unsafe fn join_fold_thread(data: *mut FoldData) -> i32 {
    #[requires(fold_data_full(data))]
    #[ensures(true)]
    platform::threading::join((*data).thread);

    let result = (*data).acc;
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

unsafe fn sum_function(acc: i32, x: i32) -> i32 {
    #[ensures(true)]
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32 {
    #[ensures(true)]
    acc ^ fac(x)
}

unsafe fn print_i32(value: i32) {
    #[ensures(true)]
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