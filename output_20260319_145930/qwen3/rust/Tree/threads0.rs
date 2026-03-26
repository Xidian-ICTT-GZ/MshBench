//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let tree = Tree::make(22);
        let sum = Tree::compute_sum_fibs(tree);
        
        print_u64(sum)
    }
}

/*@ pred tree(?t, ?d) =
    t == 0 ?
        true
    :
        alloc_block_t(t, std::alloc::Layout::new::<Tree>()) &*&
        struct_Tree_padding(t) &*&
        (*t).value |-> ?v &*&
        (*t).left |-> ?l &*&
        (*t).right |-> ?r &*&
        v == 5000 &*&
        tree(l, d - 1) &*&
        tree(r, d - 1);
@*/

//@ req depth <= 255;
//@ ens tree(result, depth);
unsafe fn Tree::make(depth: u8) -> *mut Tree
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
        //@ close tree(t, depth);
        (*t).left = left;
        (*t).right = right;
        (*t).value = value;
        
        t
    }
}

//@ req tree(tree, _);
//@ ens true;
unsafe fn Tree::compute_sum_fibs(tree: *mut Tree) -> u64
{
    if tree.is_null() {
        0
    } else {
        //@ open tree(tree, _);
        let left_sum = Self::compute_sum_fibs((*tree).left);
        let f = wrapping_fib((*tree).value);
        let right_sum = Self::compute_sum_fibs((*tree).right);
        
        left_sum.wrapping_add(f).wrapping_add(right_sum)
    }
}

//@ req true;
//@ ens true;
unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv k <= n && k >= 2;
            
            
            if k == n { break; }
            
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

//@ req true;
//@ ens true;
unsafe fn print_u64(value: u64)
{
    println!("{}", value);
}