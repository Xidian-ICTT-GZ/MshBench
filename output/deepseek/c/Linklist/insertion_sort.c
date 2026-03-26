/*@
predicate list_node(struct list_node *node; int value, struct list_node *next) =
    node->value |-> value &*& node->next |-> next &*& malloc_block_list_node(node);
@*/

/*@
predicate lseg(struct list_node *first, struct list_node *last; list<int> values) =
    first == last ?
        values == nil
    :
        first->value |-> ?v &*& first->next |-> ?nxt &*& malloc_block_list_node(first) &*& lseg(nxt, last, ?vs) &*& values == cons(v, vs);
@*/

/*@
predicate list(struct list_node *first; list<int> values) =
    first == 0 ?
        values == nil
    :
        first->value |-> ?v &*& first->next |-> ?nxt &*& malloc_block_list_node(first) &*& list(nxt, ?vs) &*& values == cons(v, vs);
@*/

/*@
lemma void lseg_append(struct list_node *first, struct list_node *last)
requires lseg(first, last, ?vs1) &*& list(last, ?vs2);
ensures list(first, append(vs1, vs2));
{
    open lseg(first, last, vs1);
    if (first == last) {
        open list(last, vs2);
        close list(first, vs2);
    } else {
        lseg_append(first->next, last);
        close list(first, append(vs1, vs2));
    }
}
@*/

/*@
lemma void list_split(struct list_node *first)
requires list(first, ?vs) &*& vs != nil;
ensures list_node(first, ?v, ?nxt) &*& list(nxt, ?vs_tail) &*& vs == cons(v, vs_tail);
{
    open list(first, vs);
}
@*/

/*@
lemma void list_merge(struct list_node *first)
requires list_node(first, ?v, ?nxt) &*& list(nxt, ?vs_tail);
ensures list(first, cons(v, vs_tail));
{
    close list(first, cons(v, vs_tail));
}
@*/

/*@
fixpoint bool sorted(list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(x, xs0): return sorted(xs0) && all_smaller_or_equal(x, xs0);
    }
}
@*/

/*@
fixpoint bool all_smaller_or_equal(int x, list<int> xs) {
    switch (xs) {
        case nil: return true;
        case cons(y, ys): return x <= y && all_smaller_or_equal(x, ys);
    }
}
@*/

/*@
lemma void sorted_append(list<int> xs, list<int> ys)
requires sorted(xs) &*& sorted(ys) &*& all_smaller_or_equal(last(xs), ys);
ensures sorted(append(xs, ys));
{
    switch (xs) {
        case nil:
        case cons(x, xs0):
            sorted_append(xs0, ys);
    }
}
@*/

/*@
fixpoint int last(list<int> xs) {
    switch (xs) {
        case nil: return 0;
        case cons(x, xs0): return xs0 == nil ? x : last(xs0);
    }
}
@*/

/*@
lemma void lseg_sorted(struct list_node *first, struct list_node *last)
requires lseg(first, last, ?vs);
ensures lseg(first, last, vs) &*& sorted(vs) == true;
{
    open lseg(first, last, vs);
    if (first != last) {
        lseg_sorted(first->next, last);
    }
}
@*/

static int compare(struct list_node *n0, struct list_node *n1)
//@ requires list_node(n0, ?v0, ?nxt0) &*& list_node(n1, ?v1, ?nxt1);
//@ ensures list_node(n0, v0, nxt0) &*& list_node(n1, v1, nxt1) &*& result == (v0 < v1 ? -1 : (v0 > v1 ? 1 : 0));
{
  if (n0->value < n1->value)
  {
    return -1;
  }
  else if (n0->value > n1->value)
  {
    return 1;
  }
  else
  {
    return 0;
  }
}

void insertion_sort_core(struct list_node **pfirst)
//@ requires *pfirst |-> ?first &*& list(first, ?values);
//@ ensures *pfirst |-> ?sorted_first &*& list(sorted_first, ?sorted_values) &*& sorted(sorted_values) == true;
{
  if (*pfirst == 0)
  {
    //@ open list(first, values);
    //@ close list(first, values);
    return;
  }

  struct list_node *last_sorted = *pfirst;
  //@ list_split(first);
  //@ struct list_node *unsorted_start = last_sorted->next;
  //@ list_merge(first);
  //@ close lseg(last_sorted, last_sorted, cons(last_sorted->value, nil));
  //@ assert lseg(last_sorted, last_sorted, ?sorted_prefix);
  //@ assert list(unsorted_start, ?unsorted_vals);
  //@ lseg_sorted(last_sorted, last_sorted);
  while (last_sorted->next != 0)
  //@ invariant *pfirst |-> ?sorted_head &*& lseg(sorted_head, last_sorted, ?sorted_vals) &*& list(last_sorted->next, ?unsorted_vals) &*& sorted(sorted_vals) == true;
  {
    struct list_node **pn = pfirst;
    //@ open lseg(sorted_head, last_sorted, sorted_vals);
    //@ struct list_node *sorted_head_val = sorted_head;
    //@ close list_node(sorted_head_val, sorted_head_val->value, sorted_head_val->next);
    //@ close lseg(sorted_head, last_sorted, sorted_vals);
    //@ list_split(last_sorted->next);
    //@ struct list_node *first_unsorted_node = last_sorted->next;
    //@ list_merge(last_sorted->next);
    int comparison = compare(*pn, last_sorted->next);
    //@ open lseg(sorted_head, last_sorted, sorted_vals);
    //@ struct list_node *current_node = sorted_head;
    //@ close list_node(current_node, current_node->value, current_node->next);
    //@ close lseg(sorted_head, last_sorted, sorted_vals);
    //@ list_split(last_sorted->next);
    //@ list_merge(last_sorted->next);

    //@ assert lseg(sorted_head, last_sorted, sorted_vals);
    //@ assert list_node(first_unsorted_node, first_unsorted_node->value, first_unsorted_node->next);
    //@ struct list_node *search_end = last_sorted->next;
    //@ close lseg(search_end, search_end, nil);
    while (pn != &(last_sorted->next) && comparison < 0)
    //@ invariant *pn |-> ?current &*& lseg(sorted_head, current, ?prefix) &*& list_node(current, ?cur_val, ?cur_next) &*& lseg(cur_next, last_sorted, ?middle) &*& list_node(first_unsorted_node, first_unsorted_node->value, first_unsorted_node->next) &*& list(last_sorted->next, unsorted_vals) &*& append(prefix, cons(cur_val, middle)) == sorted_vals &*& sorted(prefix) == true &*& all_smaller_or_equal(last(prefix), cons(cur_val, middle)) == true &*& cur_val < first_unsorted_node->value;
    {
      pn = &((*pn)->next);
      //@ open lseg(cur_next, last_sorted, middle);
      if (cur_next == last_sorted) {
        //@ close lseg(cur_next, last_sorted, middle);
        //@ assert pn == &(last_sorted->next);
      } else {
        //@ struct list_node *next_node = cur_next;
        //@ close list_node(next_node, next_node->value, next_node->next);
        //@ close lseg(cur_next, last_sorted, middle);
      }
      if (pn != &(last_sorted->next))
      {
        //@ open lseg(cur_next, last_sorted, middle);
        //@ struct list_node *new_current = *pn;
        //@ close list_node(new_current, new_current->value, new_current->next);
        //@ close lseg(cur_next, last_sorted, middle);
        //@ list_split(last_sorted->next);
        //@ list_merge(last_sorted->next);
        comparison = compare(*pn, last_sorted->next);
      }
      else
      {
      }
    }

    if (pn != &(last_sorted->next))
    {
      struct list_node *first_unsorted = last_sorted->next;
      //@ list_split(last_sorted->next);
      //@ struct list_node *unsorted_next = first_unsorted->next;
      //@ list_merge(last_sorted->next);
      last_sorted->next = first_unsorted->next;
      //@ open list(unsorted_next, ?unsorted_tail);
      //@ close list(unsorted_next, unsorted_tail);
      first_unsorted->next = *pn;
      *pn = first_unsorted;
      //@ list_split(unsorted_next);
      //@ list_merge(unsorted_next);
      //@ close lseg(first_unsorted, first_unsorted, cons(first_unsorted->value, nil));
      //@ lseg_sorted(first_unsorted, first_unsorted);
      //@ lseg_append(sorted_head, first_unsorted);
      //@ sorted_append(prefix, cons(first_unsorted->value, nil));
      //@ lseg_append(first_unsorted, last_sorted);
    }
    else
    {
      last_sorted = last_sorted->next;
      //@ list_split(last_sorted);
      //@ close lseg(last_sorted, last_sorted, cons(last_sorted->value, nil));
      //@ lseg_sorted(last_sorted, last_sorted);
      //@ lseg_append(sorted_head, last_sorted);
      //@ sorted_append(sorted_vals, cons(last_sorted->value, nil));
      //@ list_merge(last_sorted);
    }
  }
  //@ open lseg(sorted_head, last_sorted, sorted_vals);
  //@ if (sorted_head != last_sorted) {
  //@   lseg_append(sorted_head->next, last_sorted);
  //@ }
  //@ close list(sorted_head, sorted_vals);
}

struct list_node *insertion_sort(struct list_node *l)
//@ requires list(l, ?values);
//@ ensures list(result, ?sorted_values) &*& sorted(sorted_values) == true;
{
  insertion_sort_core(&l);
  return l;
}