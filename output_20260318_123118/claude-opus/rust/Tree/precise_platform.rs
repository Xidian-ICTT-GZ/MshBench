use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate tree(struct Tree* t;) =
    t != null &*&
    (t->left |-> ?l &*& t->right |-> ?r &*& t->value |-> ?v &*& tree(l) &*& tree(r))
    ||
    (t == null &*& emp);

lemma void tree_dispose(struct Tree* t)
    requires tree(t);
    ensures emp;
{
    if (t != null) {
        open tree(t);
        tree_dispose(*(t->left));
        tree_dispose(*(t->right));
        dealloc(t);
    }
}

unsafe fn random_int(max: i32) -> i32
#[requires(true)]
#[ensures(true)]
{
    max - 1 
}

unsafe fn fac(mut x: i32) -> i32
#[requires(true)]
#[ensures(true)]
{
    let mut result = 1;
    loop {
        #[invariant(true)]
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

predicate tree(struct Tree* t;)
    = t == null ? emp :
        t->left |-> ?l &*& t->right |-> ?r &*& t->value |-> ?v &*& tree(l) &*& tree(r);

impl Tree {

    unsafe fn make(depth: i32) -> *mut Tree
    #[requires(depth >= 0)]
    #[ensures(tree(result))]
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
    #[requires(tree(tree))]
    #[ensures(emp)]
    {
        if !tree.is_null() {
            Self::dispose((*tree).left);
            Self::dispose((*tree).right);
            dealloc(tree as *mut u8, Layout::new::<Tree>());
        } else {
            
        }
    }

    unsafe fn fold(tree: *mut Tree, f: FoldFunction, mut acc: i32) -> i32
    #[requires(tree(tree))]
    #[ensures(tree(tree))]
    #[ensures(true)]
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

predicate fold_data(struct FoldData* d;)
    = d->thread |-> _ &*& d->tree |-> ?t &*& d->f |-> ?f &*& d->acc |-> ?a &*& tree(t);

unsafe fn folder(data: *mut FoldData)
    #[requires(fold_data(data))]
    #[ensures(fold_data(data))]
{
    let acc = Tree::fold((*data).tree, (*data).f, (*data).acc);
    (*data).acc = acc;
}

unsafe fn start_fold_thread(tree: *mut Tree, f: FoldFunction, acc: i32) -> *mut FoldData
    #[requires(tree(tree))]
    #[ensures(fold_data(result))]
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
    #[requires(fold_data(data))]
    #[ensures(emp)]
    {
        platform::threading::join((*data).thread);
        let result = (*data).acc;
        dealloc(data as *mut u8, Layout::new::<FoldData>());
        result
    }

unsafe fn sum_function(acc: i32, x: i32) -> i32
    #[requires(true)]
    #[ensures(true)]
{
    acc + fac(x)
}

unsafe fn xor_function(acc: i32, x: i32) -> i32
    #[requires(true)]
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