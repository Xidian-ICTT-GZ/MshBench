//@ pred tree(node: *mut Tree; depth: nat) =
//@   node == 0 ?
//@     depth == 0
//@   :
//@     depth > 0 &*&
//@     struct_Tree_padding(node) &*&
//@     (*node).value |-> ?v &*&
//@     (*node).left |-> ?l &*&
//@     (*node).right |-> ?r &*&
//@     tree(l, depth - 1) &*&
//@     tree(r, depth - 1);

unsafe fn wrapping_fib(n: u16) -> u64
//@ req true;
//@ ens true;
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ open tree(_, _);
            //@ close tree(_, _);
            if k == n { break; }
            
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

struct Tree {
    left: *mut Tree,
    right: *mut Tree,
    value: u16,
}

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    //@ req true;
    //@ ens tree(result, depth as nat);
    {
        if depth == 0 {
            
            std::ptr::null_mut()
        } else {
            let left = Self::make(depth - 1);
            let right = Self::make(depth - 1);
            let value = 5000; 
            let t = alloc(Layout::new::<Tree>()) as *mut Tree;
            if t.is_null() {
                handle_alloc_error(Layout::new::<Tree>());
            }
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            //@ close tree(t, depth as nat);
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?d);
    //@ ens tree(tree, d) &*& result == result;
    {
        if tree.is_null() {
            0
        } else {
            //@ open tree(tree, _);
            let left_sum = Self::compute_sum_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_sum = Self::compute_sum_fibs((*tree).right);
            //@ close tree(tree, _);
            left_sum.wrapping_add(f).wrapping_add(right_sum)
        }
    }

}

unsafe fn print_u64(value: u64)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_fibs(tree);
        
        print_u64(sum)
    }
}