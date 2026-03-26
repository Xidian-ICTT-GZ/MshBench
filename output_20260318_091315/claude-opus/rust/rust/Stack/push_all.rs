use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(struct Node *n;) =
    n == 0 ?
        emp
    :
        n->next |-> ?next &*& n->value |-> _ &*& malloc_block_Node(n) &*& nodes(next);

predicate stack_list(struct Stack *s;) =
    s->head |-> ?head &*& nodes(head) &*& malloc_block_Stack(s);

impl Stack {

    #[requires(true)]
    #[ensures(stack_list(result))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack_list(stack))]
    #[ensures(stack_list(stack))]
    #[ensures(result == old_list_length((*stack).head))]
    unsafe fn get_count(stack: *mut Stack) -> i32
    {
        
        predicate_family fixpoint int old_list_length(struct Node *head)
        {
            head == 0 ? 0 : 1 + old_list_length((head->next))
        }

        let head = (*stack).head;
        
        let mut n = head;
        let mut i = 0;

        #[invariant(stack_list(stack) &*& nodes(n) &*& i == old_list_length(n))]
        loop {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
        
        i
    }

    #[requires(stack_list(stack))]
    #[requires(stack_list(other))]
    #[ensures(stack_list(stack))]
    #[ensures(old_list_length((*stack).head) + old_list_length((*other).head) == old_list_length((*stack).head))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());

        let mut n = head0;

        if !n.is_null() {
            #[invariant(nodes(n))]
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;
            (*stack).head = head0;
        }
    }

    #[requires(stack_list(stack))]
    #[ensures(stack_list(stack))]
    #[ensures(old_list_length((*stack).head) == old_list_length((*stack).head) + 1)] 
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_list(stack))]
    #[requires((*stack).head != std::ptr::null_mut())]
    #[ensures(stack_list(stack))]
    #[ensures(old_list_length((*stack).head) == old_list_length((*stack).head) - 1)] 
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack_list(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}