use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

predicate node<T>(n: *mut Node<T>, v: T, next: *mut Node<T>) = 
    n != std::ptr::null_mut() &*&
    n->next |-> next &*&
    n->value |-> v;

predicate list<T>(head: *mut Node<T>, contents: list<T>) =
    head == std::ptr::null_mut() ? emp : 
      exists v: T, nxt: *mut Node<T> :: 
        node(head, v, nxt) &*& list(nxt, contents.tail()) &*& contents == cons(v, contents.tail());

predicate stack<T>(s: &Stack<T>, contents: list<T>) = 
    s->head |-> ?head &*& list(head, contents);

// Lemma to transform list ownership on push/pop is not required to write explicitly here,
// owned by predicates on list and node structures.

impl<T> Stack<T> {

    #[requires(stack(this, ?contents))]
    #[ensures(stack(this, cons(value, contents)))]
    fn push(&mut self, value: T) {
        unsafe {
            let layout = Layout::new::<Node<T>>();
            let raw = alloc(layout) as *mut Node<T>;
            if raw.is_null() {
                handle_alloc_error(layout);
            }

            // Create new node owning the value and current head
            raw.write(Node {
                next: self.head,
                value,
            });

            self.head = raw;
        }
    }

    #[requires(stack(this, ?contents) &*& contents != nil)]
    #[ensures(stack(this, tail(contents)))]
    #[ensures(result == head(contents))]
    fn pop(&mut self) -> T {
        unsafe {
            let node = self.head;
            let n = &*node;
            let ret = std::ptr::read(&n.value);

            self.head = n.next;

            let layout = Layout::new::<Node<T>>();
            dealloc(node as *mut u8, layout);

            ret
        }
    }
}