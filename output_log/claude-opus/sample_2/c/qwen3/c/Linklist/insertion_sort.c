/*@ predicate list(struct list_node *head; int n, int *values) =
    head == 0 &*& n == 0 &*& values == 0 ||
    head != 0 &*&
    malloc_block_list_node(head) &*&
    head->value |-> ?v &*&
    list(head->next; ?n1, ?vals1) &*&
    n == n1 + 1 &*&
    values != 0 &*&
    malloc_block_ints(values, n) &*&
    (forall int i; 0 <= i && i < n ==> 
        values[i] == (i == 0 ? v : vals1[i-1])
    );
@*/

/*@ predicate sorted_list(struct list_node *head; int n, int *values) =
    list(head; n, values) &*&
    (forall int i; 0 <= i && i < n - 1 ==> values[i] <= values[i+1]);
@*/

/*@ lemma void list_split(struct list_node *head; int n, int *values)
    requires list(head; n, values);
    ensures exists int m, int *v1, int *v2;
        list(head; m, v1) &*&
        list(head->next; n - m, v2) &*&
        m >= 0 &*& n - m >= 0 &*&
        (forall int i; 0 <= i && i < n ==> values[i] == (i < m ? v1[i] : v2[i-m]));
@*/
/*@ proof {
    if (n == 0) {
        open list(head; n, values);
        assert values == 0;
        close list(head; 0, 0);
        return;
    }
    open list(head; n, values);
    list_split(head->next; n-1, values+1);
    close list(head; n, values);
} @*/

/*@ lemma void list_append(struct list_node *head1, struct list_node *head2;
                           int n1, int *v1, int n2, int *v2)
    requires list(head1; n1, v1) &*& list(head2; n2, v2);
    ensures list(head1; n1 + n2, ?v) &*&
            (forall int i; 0 <= i && i < n1 + n2 ==> v[i] == (i < n1 ? v1[i] : v2[i-n1]));
@*/
/*@ proof {
    if (n1 == 0) {
        open list(head1; n1, v1);
        assert head1 == 0;
        close list(head1; n2, v2);
        return;
    }
    open list(head1; n1, v1);
    list_append(head1->next, head2, n1-1, v1+1, n2, v2);
    close list(head1; n1 + n2, ?v);
} @*/

/*@ predicate insertion_sort_core_pre(struct list_node **pfirst; int n, int *values) =
    pfirst != 0 &*&
    *pfirst |-> ?head &*&
    list(head; n, values) &*&
    malloc_block_list_node(pfirst);
@*/

/*@ predicate insertion_sort_core_post(struct list_node **pfirst; int n, int *values) =
    pfirst != 0 &*&
    *pfirst |-> ?head &*&
    sorted_list(head; n, values) &*&
    malloc_block_list_node(pfirst);
@*/

/*@ requires insertion_sort_core_pre(pfirst; ?n, ?values) @*/
/*@ ensures insertion_sort_core_post(pfirst; n, values) @*/
void insertion_sort_core(struct list_node **pfirst)

{
  if (*pfirst == 0)
  {

    return;
  }

  struct list_node *last_sorted = *pfirst;
  /*@ invariant
      last_sorted != 0 &*&
      *pfirst |-> ?head &*&
      list(head; ?n_total, ?values) &*&
      list(last_sorted; ?n_sorted, ?vals_sorted) &*&
      n_sorted >= 1 &*&
      n_sorted <= n_total &*&
      (forall int i; 0 <= i && i < n_sorted ==> values[i] == vals_sorted[i]) &*&
      sorted_list(last_sorted; n_sorted, vals_sorted) &*&
      (forall int i; n_sorted <= i && i < n_total ==> values[i] == ?unsorted_vals[i - n_sorted]) &*&
      list(last_sorted->next; n_total - n_sorted, unsorted_vals);
  @*/
  while (last_sorted->next != 0)

  {

    struct list_node **pn = pfirst;

    int comparison = compare(*pn, last_sorted->next);

    /*@ invariant
        pn != 0 &*&
        *pn |-> ?cur &*&
        cur != 0 &*&
        list(*pfirst; ?n_total, ?values) &*&
        list(last_sorted; ?n_sorted, ?vals_sorted) &*&
        sorted_list(last_sorted; n_sorted, vals_sorted) &*&
        n_sorted >= 1 &*&
        n_sorted <= n_total &*&
        (forall int i; 0 <= i && i < n_sorted ==> values[i] == vals_sorted[i]) &*&
        (forall int i; n_sorted <= i && i < n_total ==> values[i] == ?unsorted_vals[i - n_sorted]) &*&
        list(last_sorted->next; n_total - n_sorted, unsorted_vals) &*&
        (forall int j; 0 <= j && j < n_sorted ==> values[j] <= last_sorted->next->value) ==>
            (pn == &(last_sorted->next) || (*pn) != 0 && (*pn)->value > last_sorted->next->value) &*&
        (pn != &(last_sorted->next) ==> comparison < 0) &*&
        (pn == &(last_sorted->next) ==> comparison >= 0);
    @*/
    while (pn != &(last_sorted->next) && comparison < 0)

    {

      pn = &((*pn)->next);

      if (pn != &(last_sorted->next))
      {

        comparison = compare(*pn, last_sorted->next);
      }
      else
      {
      }
    }

    if (pn != &(last_sorted->next))
    {
      struct list_node *first_unsorted = last_sorted->next;

      last_sorted->next = first_unsorted->next;

      first_unsorted->next = *pn;
      *pn = first_unsorted;
    }
    else
    {

      last_sorted = last_sorted->next;
    }
  }
}

/*@ requires list(l; ?n, ?values) @*/
/*@ ensures sorted_list(result; n, values) @*/
struct list_node *insertion_sort(struct list_node *l)

{
  insertion_sort_core(&l);
  return l;
}

/*@ requires \valid(x) &*& \valid(y) @*/
/*@ ensures \result == -1 <==> x->value < y->value @*/
/*@ ensures \result == 0  <==> x->value == y->value @*/
/*@ ensures \result == 1  <==> x->value > y->value @*/
static int compare(struct list_node *x, struct list_node *y)

{
  if (x->value < y->value)
  {
    return -1;
  }
  else if (x->value > y->value)
  {
    return 1;
  }
  else
  {
    return 0;
  }
}