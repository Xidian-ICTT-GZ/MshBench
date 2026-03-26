//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let tree = Tree::make(22);
        
        

        
        let sum_join_handle = spawn(Tree::compute_sum_fibs, tree);
        
        

        
        let product_join_handle = spawn(Tree::compute_product_fibs, tree);
        
        let sum = join(sum_join_handle);
        
        
        let product = join(product_join_handle);
        
        
        Tree::dispose(tree);
        
        print_u64(sum);
        print_u64(product);
    }
}

/*@ pred tree(?t, ?d) =
    t == 0 ?
        true
    :
        alloc_block(t as *u8, std::alloc::Layout::new::<Tree>()) &*&
        struct_Tree_padding(t) &*&
        (*t).value |-> ?v &*&
        (*t).left |-> ?l &*&
        (*t).right |-> ?r &*&
        v == 5000 &*&
        tree(l, if d > 0 then d - 1 else 0) &*&
        tree(r, if d > 0 then d - 1 else 0);
@*/

//@ req true;
//@ ens tree(result, depth);
unsafe fn Tree::make(depth: u8) -> *mut Tree {
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
//@ ens result == 0 ? true : (tree(tree, d) &*& result == _);
unsafe fn Tree::compute_sum_fibs(tree: *mut Tree) -> u64 {
    if tree.is_null() {
        0
    } else {
        //@ open tree(tree, ?d);
        let left_sum = Self::compute_sum_fibs((*tree).left);
        let f = wrapping_fib((*tree).value);
        let right_sum = Self::compute_sum_fibs((*tree).right);
        //@ close tree(tree, d);
        left_sum.wrapping_add(f).wrapping_add(right_sum)
    }
}

//@ req tree(tree, ?d);
//@ ens result == 1 ? true : (tree(tree, d) &*& result == _);
unsafe fn Tree::compute_product_fibs(tree: *mut Tree) -> u64 {
    if tree.is_null() {
        1
    } else {
        //@ open tree(tree, ?d);
        let left_product = Self::compute_product_fibs((*tree).left);
        let f = wrapping_fib((*tree).value);
        let right_product = Self::compute_product_fibs((*tree).right);
        //@ close tree(tree, d);
        left_product.wrapping_mul(f).wrapping_mul(right_product)
    }
}

//@ req tree(tree, ?d);
//@ ens true;
unsafe fn Tree::dispose(tree: *mut Tree) {
    
    if !tree.is_null() {
        //@ open tree(tree, ?d);
        Self::dispose((*tree).left);
        Self::dispose((*tree).right);
        dealloc(tree as *mut u8, Layout::new::<Tree>());
    }
}

//@ req true;
//@ ens true;
unsafe fn print_u64(value: u64) {
    println!("{}", value);
}

//@ req true;
//@ ens true;
unsafe fn spawn<A, R>(f: Spawnee<A, R>, arg: A) -> JoinHandle<Sendable<R>>
where A: 'static, R: 'static {
    let package = Sendable { payload: arg };
    std::thread::spawn(move || {
        let package_moved = package;
        Sendable { payload: f(package_moved.payload) }
    })
}

//@ req true;
//@ ens true;
unsafe fn join<R>(h: JoinHandle<Sendable<R>>) -> R {
    h.join().unwrap().payload
}

//@ req true;
//@ ens true;
unsafe fn wrapping_fib(n: u16) -> u64 {
    if n <= 1 {
        1
    } else {
        let mut k: u16 = 2;
        let mut fib_k_minus_1: u64 = 1;
        let mut fib_k: u64 = 1;
        loop {
            //@ inv k <= n + 1 &*& fib_k_minus_1 >= 1 &*& fib_k >= 1;
            if k == n { break; }
            
            let fib_k_plus_1 = fib_k_minus_1.wrapping_add(fib_k);
            
            k += 1;
            fib_k_minus_1 = fib_k;
            fib_k = fib_k_plus_1;
        }
        fib_k
    }
}