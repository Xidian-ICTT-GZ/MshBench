#[predicate]
pub unsafe fn nodes(n: *mut Node) = 
    n != std::ptr::null_mut() ?
      n->next |-> ?next &*& nodes(next)
    : true;

#[predicate]
pub unsafe fn stack(s: *mut Stack) = 
    s->head |-> ?head &*& nodes(head);

impl Stack {
  #[requires(stack: stack(stack) &*& other: stack(other))]
  #[ensures(stack: stack(stack))]
  unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
  {
    let head0 = (*other).head;
    dealloc(other as *mut u8, core::alloc::Layout::new::<Stack>());
    let mut n = head0;

    if !n.is_null() {
        #[invariant(n != std::ptr::null_mut() ? nodes(n) &*& old_head0_trail(n, head0) : true)]
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
}

#[predicate]
pub unsafe fn old_head0_trail(curr: *mut Node, head0: *mut Node) =
    curr != std::ptr::null_mut() ?
        curr->next |-> ?next &*& (
            (curr == head0 ? true : old_head0_trail(next, head0))
        )
    : false;