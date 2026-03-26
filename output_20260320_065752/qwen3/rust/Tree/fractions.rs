/*@ pred tree(?t, ?d) =
    t == 0 ?
        true
    :
        alloc_block(t, std::alloc::Layout::new::<Tree>()) &*&
        struct_Tree_padding(t) &*&
        (*t).value |-> ?v &*&
        (*t).left |-> ?l &*&
        (*t).right |-> ?r &*&
        v == 5000 &*&
        tree(l, if d > 0 then d - 1 else 0) &*&
        tree(r, if d > 0 then d - 1 else 0);
@*/

//@ req true;
//@ ens true;
fn main()
{
    unsafe {
        let tree = Tree::make(22);
        
        

        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        

        
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        
        
        
        let product = join(product_join_handle);
        
        
        
        print_u64(sum);
        print_u64(product);
    }
}

//@ req true;
//@ ens true;
unsafe fn print_u64(value: u64)
{
    println!("{}", value);
}

impl Tree {

    //@ req d <= 255;
    //@ ens tree(result, d);
    unsafe fn make(depth: u8) -> *mut Tree
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

    //@ req tree(tree, ?d);
    //@ ens tree(tree, d) &*& result == Tree::compute_sum_fibs_spec(tree);
    unsafe fn compute_sum_fibs(tree: *mut Tree) -> u64
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
    
    //@ req tree(tree, ?d);
    //@ ens tree(tree, d) &*& result == Tree::compute_product_fibs_spec(tree);
    unsafe fn compute_product_fibs(tree: *mut Tree) -> u64
    {
        if tree.is_null() {
            1
        } else {
            //@ open tree(tree, _);
            let left_product = Self::compute_product_fibs((*tree).left);
            let f = wrapping_fib((*tree).value);
            let right_product = Self::compute_product_fibs((*tree).right);
            //@ close tree(tree, _);
            left_product.wrapping_mul(f).wrapping_mul(right_product)
        }
    }
    
}

/*@ fixpoint u64 compute_sum_fibs_spec(*mut Tree t) {
    if t == 0 then 0
    else compute_sum_fibs_spec((*(t)).left) + wrapping_fib_spec((*(t)).value) + compute_sum_fibs_spec((*(t)).right)
} @*/

/*@ fixpoint u64 compute_product_fibs_spec(*mut Tree t) {
    if t == 0 then 1
    else compute_product_fibs_spec((*(t)).left) * wrapping_fib_spec((*(t)).value) * compute_product_fibs_spec((*(t)).right)
} @*/

/*@ fixpoint u64 wrapping_fib_spec(u16 n) {
    if n <= 1 then 1
    else wrapping_fib_spec(n - 1) + wrapping_fib_spec(n - 2)
} @*/

//@ req true;
//@ ens result == wrapping_fib_spec(n);
unsafe fn wrapping_fib(n: u16) -> u64
{
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv k <= n &*& fib_k_minus_1 == wrapping_fib_spec(k - 1) &*& fib_k == wrapping_fib_spec(k);
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
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static
{
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

//@ req true;
//@ ens true;
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R
{
    h.join().unwrap().payload
}