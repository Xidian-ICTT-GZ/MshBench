typedef struct node
{
	int item;
	struct node *next;
	struct node *prev;
} *node;

typedef struct dllist
{
	node head;
	node tail;
} *dllist;

//@ requires true;
//@ ensures true;
void reverse(dllist arg)
{
	node ptr = arg->head;
	node temp1 = 0;
	node temp2 = 0;

	while (ptr != 0)
	{
		temp1 = ptr->next;
		temp2 = ptr->prev;
		ptr->next = temp2;
		ptr->prev = temp1;

		ptr = temp1;
	}

	temp1 = arg->head;
	temp2 = arg->tail;
	arg->head = temp2;
	arg->tail = temp1;
}