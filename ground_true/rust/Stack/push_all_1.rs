/*@
lem lseg_append_lemma(first: *mut Node)
req lseg(first, ?n, ?count) &*& lseg(n, 0, ?count0);
ens lseg(first, 0, count + count0);
{
open lseg(first, n, count);
if first != n {
open lseg(n, 0, count0);
close lseg(n, 0, count0);
lseg_append_lemma((*first).next);
close lseg(first, 0, count + count0);
}
}
@*/
impl Stack {
unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
//@ req Stack(stack, ?count) &*& Stack(other, ?count0);
//@ ens Stack(stack, count0 + count);
{
//@ open Stack(stack, count);
//@ Nodes_to_lseg_lemma((*stack).head);
//@ open Stack(other, count0);
//@ Nodes_to_lseg_lemma((*other).head);
let head0 = (*other).head;
dealloc(other as *mut u8, Layout::new::<Stack>());
let mut n = head0;
//@ open lseg(head0, 0, count0);
if !n.is_null() {
//@ close lseg(head0, head0, 0);
loop {
/*@
inv lseg(head0, n, ?count1) &*& n != 0 &*& (*n).value |-> ?n_value &*&
(*n).next |-> ?next &*&
alloc_block_Node(n) &*&
lseg(next, 0, count0 - count1 - 1);
@*/
if (*n).next.is_null() {
break;
}
n = (*n).next;
//@ lseg_add_lemma(head0);
//@ open lseg(next, 0, count0 - count1 - 1);
}
//@ open lseg(0, 0, _);
(*n).next = (*stack).head;
//@ lseg_add_lemma(head0);
//@ lseg_append_lemma(head0);
(*stack).head = head0;
}
//@ lseg_to_Nodes_lemma((*stack).head);
//@ close Stack(stack, count0 + count);
}
}