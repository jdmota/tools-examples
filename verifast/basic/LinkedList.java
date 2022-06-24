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

  public void insert(FileReader f, int index)
    //@ requires llist(this, _, _, ?list) &*& 0 <= index && index <= length(list);
    //@ ensures llist(this, _, _, append(take(index, list), cons(f, drop(index, list))));
  {
    //@ open llist(this, ?h, ?t, list);
    if (index == 0) {
      Node newNode = new Node();
      newNode.value = f;
      newNode.next = head;
      //@ close node(newNode, head, f);
      if (head == null) {
        head = newNode;
        tail = newNode;
      } else {
        //@ open lseg(h, t, ?ht);
        //@ distinct_nodes(newNode, h);
        //@ distinct_nodes(newNode, t);
        //@ close lseg(h, t, ht);
        //@ close lseg(newNode, t, cons(f, ht));
        head = newNode;
      }
      return;
    }

    //@ assert 0 < index;
    //@ assert lseg(h, t, ?ht);
    //@ assert node(t, null, ?tv);
    //@ append_inversion(ht, tv);

    Node prev = head;

    /*@
    if (prev == t) {
      assert h == t;
      empty_seq(h);
      assert node(t, null, tv);
      assert list == append(nil, cons(tv, nil));
      assert list == cons(tv, nil);
      assert lseg(h, t, nil) &*&
        node(t, null, tv) &*&
        take(0, list) == nil &*&
        nth(0, list) == tv &*&
        drop(1, list) == nil;
    } else {
      assert lseg(h, prev, ?l1) &*&
        node(prev, ?prevnext, ?pv) &*&
        lseg(prevnext, t, ?l2) &*&
        node(t, null, ?v) &*&
        take(0, list) == l1 &*&
        nth(0, list) == pv &*&
        drop(1, list) == append(l2, cons(v, nil));
    }
    @*/

    int i = 1;
    while (i < index)
      /*@ invariant 1 <= i &*& i <= index &*& head |-> h &*& tail |-> t &*& h != null &*& t != null &*& prev != null &*&
            (prev == t ?
              (
                lseg(h, t, ht) &*&
                node(t, null, tv) &*&
                take(i - 1, list) == ht &*&
                nth(i - 1, list) == tv &*&
                drop(i, list) == nil &*&
                i == length(list)
              ) :
              (
                lseg(h, prev, ?l1) &*&
                node(prev, ?prevnext, ?pv) &*&
                lseg(prevnext, t, ?l2) &*&
                node(t, null, tv) &*&
                take(i - 1, list) == l1 &*&
                nth(i - 1, list) == pv &*&
                drop(i, list) == append(l2, cons(tv, nil)) &*&
                i <= length(list)
              )
            );
      @*/
    {
      //@ append_take_nth_drop(i - 1, list);
      Node nextPrev = prev.next;
      /*@
      if (nextPrev == null) {
        if (prev == t) {
          assert false;
        } else {
          open lseg(nextPrev, _, _);
          open node(nextPrev, _, _);
          assert false;
        }
      }
      @*/
      /*@
      if (nextPrev == t) {
        empty_seq(nextPrev);
        close node(prev, nextPrev, ?pv);
        add_lemma(h, prev, nextPrev);
        assert length(drop(i, list)) == 1;
        length_drop(i, list);
        assert i + 1 == length(list);
        take_one_more(i - 1, list);
      } else {
        close node(prev, nextPrev, ?pv);
        add_lemma(h, prev, nextPrev);
        take_one_more(i - 1, list);
        drop_n_plus_one(i, list);
      }
      @*/
      prev = nextPrev;
      i++;
    }

    Node newNode = new Node();
    newNode.value = f;
    if (prev == tail) {
      //@ assert lseg(h, t, ht);
      //@ close node(newNode, null, f);
      //@ open node(t, null, tv);
      tail.next = newNode;
      //@ close node(t, newNode, tv);
      //@ add_lemma(h, t, newNode);
      tail = newNode;
      //@ assert index == length(list);
      //@ assert take(index, list) == list;
      //@ assert take(index - 1, list) == ht;
      //@ drop_n_plus_one(i - 1, list);
      //@ assert drop(index - 1, list) == cons(tv, nil);
      //@ assert list == append(ht, cons(tv, nil));
    } else {
      //@ open lseg(h, prev, ?hp);
      //@ distinct_nodes(newNode, h);
      //@ distinct_nodes(newNode, t);
      //@ close lseg(h, prev, hp);
      //@ open node(prev, ?prevnext, ?pv);
      //@ assert lseg(prevnext, t, ?pt);
      newNode.next = prev.next;
      //@ close node(newNode, prevnext, f);
      prev.next = newNode;
      //@ close node(prev, newNode, pv);
      //@ add_lemma(h, prev, newNode);
      //@ close lseg(newNode, t, _);
      //@ lseg_concat(h, newNode, t);
      //@ append_assoc(append(hp, cons(pv, nil)), cons(f, pt), cons(tv, nil));
      //@ take_one_more(index - 1, list);
      //@ assert (append(hp, cons(pv, nil)) == take(index, list));
      //@ assert (append(cons(f, pt), cons(tv, nil)) == cons(f, drop(index, list)));
    }
  }
}
