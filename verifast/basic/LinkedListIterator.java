/*@
// nodes is a predicate that talks about all the nodes starting on n and following the next pointer

predicate nodes(Node n; list<FileReader> list) =
  n == null ? list == nil : (node(n, ?next, ?value) &*& nodes(next, ?l) &*& list == cons(value, l));

predicate iterator_base(LinkedList javalist, Node n; list<FileReader> list, list<FileReader> a, list<FileReader> b) =
  [1/2]javalist.head |-> ?h &*& [1/2]javalist.tail |-> ?t &*&
  [1/2]llist(javalist, h, t, list) &*& [1/2]lseg(h, n, a) &*& [1/2]nodes(n, b) &*& list == append(a, b);

predicate iterator(LinkedList javalist, LinkedListIterator it, Node n; list<FileReader> list, list<FileReader> a, list<FileReader> b) =
  it.curr |-> n &*& iterator_base(javalist, n, list, a, b);
@*/

public class LinkedListIterator {

  private Node curr;

  public LinkedListIterator(LinkedList javalist, Node head)
    //@ requires llist(javalist, head, _, ?list);
    //@ ensures iterator(javalist, this, head, list, nil, list);
  {
    curr = head;
    //@ prepare_iterator(javalist);
    //@ close iterator(javalist, this, head, list, nil, list);
  }

  public boolean hasNext()
    //@ requires iterator(?javalist, this, ?n, ?list, ?a, ?b);
    /*@ ensures iterator(javalist, this, n, list, a, b) &*&
                result ? n != null &*& b != nil : n == null &*& b == nil &*& a == list; @*/
  {
    //@ open iterator(javalist, this, n, list, a, b);
    //@ open iterator_base(javalist, n, list, a, b);
    //@ open nodes(_, _);
    return curr != null;
    //@ close iterator(javalist, this, n, list, a, b);
  }

  public FileReader next()
    //@ requires iterator(?javalist, this, ?n, ?list, ?a, ?b) &*& n != null;
    //@ ensures iterator(javalist, this, _, list, append(a, cons(head(b), nil)), drop(1, b)) &*& result == head(b);
  {
    //@ open iterator(javalist, this, n, list, a, b);
    //@ open nodes(n, b);
    FileReader value = curr.value;
    curr = curr.next;
    return value;
    //@ assert append(take(1, b), drop(1, b)) == b;
    //@ assert append(a, append(take(1, b), drop(1, b))) == append(a, b);
    //@ append_assoc(a, take(1, b), drop(1, b));
    //@ assert append(append(a, take(1, b)), drop(1, b)) == append(a, b);
    //@ append_cons_not_nil(a, n.value, drop(1, b));
    //@ assert list != nil;
    //@ close [1/2]node(n, ?next, ?val);
    //@ open llist(_, ?h, ?t, _);
    //@ iterator_advance(h, n, t);
    //@ close iterator(javalist, this, next, list, append(a, cons(val, nil)), drop(1, b));
  }

}
