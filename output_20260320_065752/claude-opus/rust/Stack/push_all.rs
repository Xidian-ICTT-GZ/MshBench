use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@

predicate_node_ptr(Node* n) = n != 0 &*& struct Node { next: Node* next; value: int value; }(n, ?next, ?value) &*& predicate_node_ptr(next);

predicate stack(?head) = 
    head == 0 ? emp : predicate_node_ptr(head);

@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {

    //@ req true;
    //@ ens result != 0 &*& stack(result, _);
    unsafe fn create() -> *mut Stack
    
    
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }

        //@ close stack(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        
        
        stack
    }

    //@ req stack(stack, ?head);
    //@ ens stack(stack, head) &*& result == (count_list(head));
    unsafe fn get_count(stack: *mut Stack) -> i32
    
    
    {
        
        let head = (*stack).head;
        
        let mut n = head;
        let mut i = 0;
        
        //@ open stack(stack, head);
        //@ open predicate_node_ptr(n);
        loop {
            //@ if (n == std::ptr::null_mut()) { break; }
            
            if n.is_null() {
                break;
            }
            
            n = (*n).next;
            i += 1;
            //@ open predicate_node_ptr(n);
        }
        //@ close stack(stack, head);
        
        
        
        i
    }

    //@ req stack(stack, ?head1) &*& stack(other, ?head2);
    //@ ens stack(stack, head2_head_plus_head1(head2, head1)) &*& true;
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    
    
    {
        
        let head0 = (*other).head;
        //@ open stack(other, head0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        //@ close stack(other, std::ptr::null_mut());
        let mut n = head0;
        
        if !n.is_null() {
            
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

    //@ req stack(stack, ?head);
    //@ ens stack(stack, cons(value, head));
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

    //@ req stack(stack, cons(?v, ?tail));
    //@ ens stack(stack, tail) &*& result == v;
    unsafe fn pop(stack: *mut Stack) -> i32
    
    
    {
        
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    //@ req stack(stack, ?head);
    //@ ens true;
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

//@ predicate stack(Stack* s, Node* head) = s->head |-> head &*& nodes(head);
//@ predicate nodes(Node* n) = n == 0 ? emp : n->next |-> ?next &*& n->value |-> _ &*& nodes(next);
//@ fixpoint int count_list(Node* n) { return n == 0 ? 0 : 1 + count_list(n->next); }
//@ fixpoint Node* head2_head_plus_head1(Node* head2, Node* head1) { return head2 == 0 ? head1 : head2; }
//@ fixpoint list<int> cons(int v, list<int> l) { return cons(v, l); }