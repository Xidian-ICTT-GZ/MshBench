use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*mut Node n; list<i32> vs) =
    if n == std::ptr::null_mut() {
        vs == []
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?v &*& Nodes(next, ?tail_vs) &*& vs == cons(v, tail_vs)
    };

predicate Stack_own(*mut Stack s; list<i32> vs) =
    (*s).head |-> ?head &*& Nodes(head, vs);

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
    #[requires(Nodes(n, ?vs) &*& data |-> ?d)]
    #[ensures(Nodes(n, ?vs') &*& data |-> d &*& vs' == map(f, vs, d))]
{
    
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
    
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(Nodes(n, _))]
    #[ensures(true)]
{
    
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        #[requires(true)]
        #[ensures(Stack_own(result, []))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        
        
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(Stack_own(stack, ?vs))]
        #[ensures(Stack_own(stack, cons(value, vs)))]
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(Stack_own(stack, cons(?v, ?vs)))]
        #[ensures(Stack_own(stack, vs) &*& result == v)]
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
        #[requires(Stack_own(stack, ?vs) &*& data |-> ?d)]
        #[ensures(Stack_own(stack, ?vs') &*& data |-> d &*& vs' == map(f, vs, d))]
    {
        
        map_nodes((*stack).head, f, data);
        
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires(Stack_own(stack, _))]
        #[ensures(true)]
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
    #[requires(data |-> ?a)]
    #[ensures(data |-> a &*& result == x + a)]
{
    
    let result = x + *(data as *mut i32);
    
    result
}

unsafe fn read_i32() -> i32
    #[requires(true)]
    #[ensures(true)]
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
    #[requires(true)]
    #[ensures(true)]
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        

        
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        
        Stack::dispose(s);
    }
}