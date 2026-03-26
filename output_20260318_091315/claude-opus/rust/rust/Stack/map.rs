use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(struct Node* n;) =
    n->next |-> ?nx &*& n->value |-> ?v &*& malloc_block_Node(n);

predicate nodes(struct Node* n;) =
    n == null ? true : node(n) &*& nodes(n->next);

predicate stack(struct Stack* s;) =
    s->head |-> ?h &*& nodes(h) &*& malloc_block_Stack(s);

typedef I32Func = (unsafe fn(*mut u8, i32) -> i32);

#[requires(nodes(n))]
#[ensures(nodes(n))]
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
    
    
    

{
    if n != std::ptr::null_mut() {
        node(n);
        drop nodes(n->next);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        close nodes(n->next);
        close node(n);
    }
}

#[requires(nodes(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node)
    
    

{
    if n != std::ptr::null_mut() {
        node(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack
    
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        close stack(stack);
        return stack;
    }

    #[requires(stack(stack_ptr))]
    #[ensures(stack(stack_ptr))]
    unsafe fn push(stack_ptr: *mut Stack, value: i32)
    
    
    
    {
        open stack(stack_ptr);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack_ptr).head;
        (*n).value = value;
        (*stack_ptr).head = n;

        close node(n);
        close nodes(n);
        close stack(stack_ptr);
    }

    #[requires(stack(stack_ptr) &*& (*stack_ptr).head != std::ptr::null_mut())]
    #[ensures(stack(stack_ptr))]
    #[ensures(old(stack(stack_ptr)))]
    unsafe fn pop(stack_ptr: *mut Stack) -> i32
    
    
    
    {
        open stack(stack_ptr);
        let head = (*stack_ptr).head;
        node(head);
        open nodes(head->next);

        let result = (*head).value;
        (*stack_ptr).head = (*head).next;
        close nodes((*stack_ptr).head);

        dealloc(head as *mut u8, Layout::new::<Node>());

        close stack(stack_ptr);
        return result;
    }

    #[requires(stack(stack_ptr))]
    #[ensures(stack(stack_ptr))]
    unsafe fn map(stack_ptr: *mut Stack, f: I32Func, data: *mut u8)
    {
        open stack(stack_ptr);
        map_nodes((*stack_ptr).head, f, data);
        close stack(stack_ptr);
    }

    #[requires(stack(stack_ptr))]
    #[ensures(true)]
    unsafe fn dispose(stack_ptr: *mut Stack)
    {
        open stack(stack_ptr);
        dispose_nodes((*stack_ptr).head);
        dealloc(stack_ptr as *mut u8, Layout::new::<Stack>());
    }

}

#[requires(true)]
#[ensures(true)]
unsafe fn plus_a(data: *mut u8, x: i32) -> i32
{
    let result = x + *(data as *mut i32);
    result
}

unsafe fn read_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
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