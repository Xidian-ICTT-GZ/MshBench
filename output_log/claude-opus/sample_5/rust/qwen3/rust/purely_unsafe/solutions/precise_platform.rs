use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred] 
pred tree_ptr(t: *mut Tree) = 
    t != 0 ? 
        exists<left: *mut Tree, right: *mut Tree, value: i32> (
            t |-> Tree { left: left, right: right, value: value } *
            tree_ptr(left) *
            tree_ptr(right)
        ) :
        emp;

#[pred]
pred fold_data_ptr(d: *mut FoldData) =
    d != 0 ?
        d |-> FoldData { thread: _, tree: t, f: _, acc: _ } *
        tree_ptr(t) :
        emp;

#[requires(max > 0)]
unsafe fn random_int(max: i32) -> i32 {
    max - 1
}

#[requires(x >= 1)]
#[ensures(result == factorial(x))]
unsafe fn fac(mut x: i32) -> i32 {
    let mut result = 1;
    let x0 = x;
    #[invariant(x >= 1 && result == factorial(x0) / factorial(x - 1))]
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

#[pure]
fn tree_height(t: *mut Tree) -> i32 {
    if t == 0 { 0 } else { 1 + std::cmp::max(tree_height(unsafe { (*t).left }), tree_height(unsafe { (*t).right })) }
}

#[pure]
fn fold_tree(t: *mut Tree, f: FoldFunction, acc: i32) -> i32 {
    if t == 0 { acc }
    else {
        let acc1 = fold_tree(unsafe { (*t).left }, f, acc);
        let acc2 = fold_tree(unsafe { (*t).right }, f, acc1);
        f(acc2, unsafe { (*t).value })
    }
}

impl Tree {
    #[requires(depth >= 0)]
    #[ensures(result != 0 ==> tree_ptr(result) && tree_height(result) == depth)]
    unsafe fn make(depth: i32) -> *mut Tree {
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
            // Allocate node
            *t = Tree { left: left, right: right, value: value };

            t
        }
    }

    #[requires(tree != 0 ==> tree_ptr(tree))]
    #[ensures(emp)]
    unsafe fn dispose(tree: *mut Tree) {
        if !tree.is_null() {
            // Unfold tree_ptr to get ownership of children pointers
            open tree_ptr(tree);
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            close tree_ptr(tree);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        }
    }

    #[requires(tree != 0 ==> tree_ptr(tree))]
    #[ensures(result == fold_tree(tree, f, acc))]
    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32 {
        if tree.is_null() {
            acc
        } else {
            open tree_ptr(tree);
            acc = Self::fold((*tree).left, f, acc);
            acc = Self::fold((*tree).right, f, acc);
            acc = f(acc, (*tree).value);
            close tree_ptr(tree);
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

#[requires(data != 0 && fold_data_ptr(data))]
#[ensures((*data).acc == fold_tree((*data).tree, (*data).f, (*data).acc))]
unsafe fn folder(data: *mut FoldData) {
    open fold_data_ptr(data);
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
    close fold_data_ptr(data);
}

#[requires(tree != 0 ==> tree_ptr(tree))]
#[ensures(result != 0 ==> fold_data_ptr(result))]
unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData {
    let data = alloc(Layout::new::<FoldData>()) as *mut FoldData;
    if data.is_null() {
        handle_alloc_error(Layout::new::<FoldData>());
    }
    *data = FoldData { thread: unsafe { std::mem::zeroed() }, tree: tree, f: f, acc: acc };
    close fold_data_ptr(data);

    let t = platform::threading::fork_joinable(folder, data);
    open fold_data_ptr(data);
    (*data).thread = t;
    close fold_data_ptr(data);
    data
}

#[requires(data != 0 && fold_data_ptr(data))]
#[ensures(result == (*data).acc)]
unsafe fn join_fold_thread(data: *mut FoldData) -> i32 {
    open fold_data_ptr(data);
    platform::threading::join((*data).thread);

    let result = (*data).acc;
    close fold_data_ptr(data);
    dealloc(data as *mut u8, Layout::new::<FoldData>());
    result
}

#[requires(acc >= 0 && x >= 1)]
#[ensures(result == acc + factorial(x))]
unsafe fn sum_function(acc: i32, x: i32) -> i32 {
    acc + fac(x)
}

#[requires(acc >= 0 && x >= 1)]
#[ensures(result == acc ^ factorial(x))]
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

// Pure helper predicates (must be defined for VeriFast)
#[pure]
fn factorial(n: i32) -> i32 {
    if n <= 1 { 1 } else { n * factorial(n - 1) }
}

#[pure]
fn tree_height(t: *mut Tree) -> i32 {
    if t == 0 { 0 } else { 1 + std::cmp::max(tree_height(unsafe { (*t).left }), tree_height(unsafe { (*t).right })) }
}

#[pure]
fn fold_tree(t: *mut Tree, f: FoldFunction, acc: i32) -> i32 {
    if t == 0 { acc }
    else {
        let acc1 = fold_tree(unsafe { (*t).left }, f, acc);
        let acc2 = fold_tree(unsafe { (*t).right }, f, acc1);
        f(acc2, unsafe { (*t).value })
    }
}