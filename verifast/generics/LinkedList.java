// Adapted from https://people.cs.kuleuven.be/~bart.jacobs/verifast/examples/iter.c.html
// One key difference from the aforementioned C code is that when the linked-list is empty,
// it has the "head" and "tail" fields with null values, instead of using a dummy node.

class Node<T> {
  T value;
  Node<T> next;
}

/*@
predicate node<T>(Node<T> node; Node<T> next, T value) =
  node.next |-> next &*& node.value |-> value;

// lseg is a predicate that talks about the list between n1 inclusive and n2 exclusive

predicate lseg<T>(Node<T> n1, Node<T> n2; list<T> list) =
  n1 == n2 ? list == nil : node<T>(n1, ?next, ?value) &*& lseg<T>(next, n2, ?l) &*& list == cons(value, l);

predicate llist<T>(LinkedList<T> javalist; Node<T> h, Node<T> t, list<T> list) =
  javalist.head |-> h &*& javalist.tail |-> t &*&
    h == null ? t == null &*& list == nil :
    t == null ? h == null &*& list == nil :
    lseg<T>(h, t, ?l) &*& node<T>(t, null, ?value) &*& list == append(l, cons(value, nil)) &*& list != nil;
@*/

public class LinkedList<T> {

  private Node<T> head;
  private Node<T> tail;
  
  public LinkedList()
    //@ requires true;
    //@ ensures llist<T>(this, null, null, nil);
  {
    head = null;
    tail = null;
  }
}
