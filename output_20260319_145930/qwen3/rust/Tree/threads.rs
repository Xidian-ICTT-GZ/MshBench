//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let tree = Tree::make(22);
        
        let left = (*tree).left;
        let right = (*tree).right;
        
        let left_join_handle = spawn(Tree::compute_sum_fibs, left);
        
        let right_join_handle = spawn(Tree::compute_sum_fibs, right);
        let root_fib = wrapping_fib((*tree).value);

        let left_sum = join(left_join_handle);
        
        let right_sum = join(right_join_handle);
        
        let sum = left_sum.wrapping_add(root_fib).wrapping_add(right_sum);
        
        print_u64(sum)
    }
}

/*@ pred tree(?t, ?d) =
    t == 0 ?
        d == 0
    :
        d > 0 &*&
        alloc_block_Tree(t) &*&
        struct_Tree_padding(t) &*&
        struct_Tree_fields(t, ?l, ?r, ?v) &*&
        v == 5000 &*&
        tree(l, d - 1) &*&
        tree(r, d - 1);
@*/

unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
//@ req true;
//@ ens true;
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
//@ req true;
//@ ens true;
{
    h.join().unwrap().payload
}

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
            //@ inv k >= 2 &*& k <= n + 1 &*& true;
            if k == n { break; }
            
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}

impl Tree {

    unsafe fn make(depth: u8) -> *mut Tree
    //@ req depth <= 22; // to avoid excessive allocation
    //@ ens tree(result, depth);
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
            //@ close struct_Tree_fields(t, left, right, value);
            //@ close struct_Tree_padding(t);
            (*t).left = left;
            (*t).right = right;
            (*t).value = value;
            t
        }
    }

    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
    //@ req tree(tree, ?d);
    //@ ens tree(tree, d) &*& result >= 0;
    {
        if tree.is_null() {
            0
        } else {
            //@ open tree(tree, d);
            //@ assert alloc_block_Tree(tree);
            //@ assert struct_Tree_fields(tree, ?l, ?r, ?v);
            let left_sum = Self::compute_sum_fibs(l);
            let f = wrapping_fib(v);
            let right_sum = Self::compute_sum_fibs(r);
            //@ close tree(tree, d);
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