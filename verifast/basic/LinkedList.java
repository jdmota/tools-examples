import java.util.Iterator;
import java.lang.Iterable;

// Adapted from https://people.cs.kuleuven.be/~bart.jacobs/verifast/examples/iter.c.html
// One key difference from the aforementioned C code is that when the linked-list is empty,
// it has the "head" and "tail" fields with null values, instead of using a dummy node.

class Node {
  FileReader value;
  Node next;
}

/*@
predicate node(Node node; Node next, FileReader value) =
  node.next |-> next &*& node.value |-> value;

// lseg is a predicate that talks about the list between n1 inclusive and n2 exclusive

predicate lseg(Node n1, Node n2; list<FileReader> list) =
  n1 == n2 ? list == nil : node(n1, ?next, ?value) &*& lseg(next, n2, ?l) &*& list == cons(value, l);

predicate llist(LinkedList javalist; Node h, Node t, list<FileReader> list) =
  javalist.head |-> h &*& javalist.tail |-> t &*&
    h == null ? t == null &*& list == nil :
    t == null ? h == null &*& list == nil :
    lseg(h, t, ?l) &*& node(t, null, ?value) &*& list == append(l, cons(value, nil)) &*& list != nil;
@*/

public class LinkedList {

  private Node head;
  private Node tail;
  
  public LinkedList()
    //@ requires true;
    //@ ensures llist(this, null, null, nil);
  {
    head = null;
    tail = null;
  }
  
  public void add(FileReader x)
    //@ requires llist(this, _, _, ?list);
    //@ ensures llist(this, _, _, append(list, cons(x, nil)));
  {
    Node n = new Node();
    n.value = x;
    n.next = null;
    if (head == null) {
      head = n;
      tail = n;
    } else {
      tail.next = n;
      //@ add_lemma(head, tail, n);
      tail = n;
    }
    //@ append_cons_not_nil(list, x, nil);
  }
  
  public FileReader remove()
    //@ requires llist(this, _, _, ?list) &*& list != nil;
    //@ ensures llist(this, _, _, ?rest) &*& list == cons(result, rest);
  {
    //@ open llist(this, _, _, _);
    //@ open lseg(head, tail, _);
    FileReader result = head.value;
    if (head == tail) {
      head = null;
      tail = null;
      //@ close llist(this, _, _, _);
    } else {
      //@ open lseg(head.next, tail, _);
      //@ open node(head.next, _, _);
      head = head.next;
      //@ close llist(this, _, _, _);
    }
    return result;
  }
  
  public boolean notEmpty()
    //@ requires llist(this, _, _, ?list);
    //@ ensures llist(this, _, _, list) &*& (result == (list != nil));
  {
    //@ open llist(_, _, _, _);
    return head != null;
    //@ close llist(_, _, _, _);
  }
  
  public LinkedListIterator iterator()
    //@ requires llist(this, ?h, _, ?list);
    //@ ensures iterator(this, result, h, list, nil, list) &*& result != null;
  {
    return new LinkedListIterator(this, head);
  }
}
