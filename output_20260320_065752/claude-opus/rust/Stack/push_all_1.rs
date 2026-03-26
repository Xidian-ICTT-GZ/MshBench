/*@ 
predicate list(struct Cell* head) =
    head == 0 ?
        true
    :
        head->next |-> ?next &*& malloc_block_Cell(head) &*& list(next);
@*/

/*@ predicate stack(struct Stack* s, struct Cell* head) =
    s->head |-> head &*& malloc_block_Stack(s) &*& list(head);
@*/

impl Stack {
    //@ req stack(stack, ?head1) &*& stack(other, ?head2);
    //@ ens stack(stack, ?head) &*& emp;
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    {
        //@ open stack(stack, ?head1);
        //@ open stack(other, ?head2);

        let head0 = (*other).head;
        //@ close stack(other, head0);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            //@ open list(head0);
            loop {
                //@ open list(n);
                if (*n).next.is_null() {
                    //@ close list(n);
                    break;
                }
                n = (*n).next;
            }
            //@ open list(n);
            (*n).next = (*stack).head;
            //@ open list((*stack).head);
            //@ close list(n);
            //@ close list(head0);
            (*stack).head = head0;
            //@ close stack(stack, head0);
        } else {
            //@ close stack(stack, (*stack).head);
        }
    }
}