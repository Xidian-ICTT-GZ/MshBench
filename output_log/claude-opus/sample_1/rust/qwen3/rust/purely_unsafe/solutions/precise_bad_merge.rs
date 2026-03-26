predicate list_node(int* p; int v, int* next) = p |-> v &*& (next == 0 ? true : p + 1 == next);

predicate linked_list(int* head; list<int> vs) =
    switch(vs) {
        case Nil: head == 0;
        case Cons(h, t): 
            head != 0 &*& list_node(head; h, head + 1) &*& linked_list(head + 1; t);
    };

#[requires(linked_list(head; vs))]
#[ensures(linked_list(head; vs))]
fn print_list(mut head: *mut i32)
    //@ requires linked_list(head; ?vs);
    //@ ensures linked_list(head; vs);
{
    while head != std::ptr::null_mut() 
        //@ invariant linked_list(head; ?vs0) &*& vs0 <= vs;
    {
        unsafe {
            let value = *head;
            let next = head.offset(1);
            head = next;
        }
    }
}