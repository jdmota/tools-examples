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

  public boolean isEmpty()
    //@ requires llist(this, _, _, ?list);
    //@ ensures llist(this, _, _, list) &*& (result == (list == nil));
  {
    //@ open llist(_, _, _, _);
    return head == null;
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
      if (head == null) {
        head = newNode;
        tail = newNode;
      } else {
        //@ open lseg(h, t, ?ht);
        //@ distinct_nodes(newNode, t);
        //@ close lseg(h, t, ht);
        //@ close lseg(newNode, t, cons(f, ht));
        head = newNode;
      }
      return;
    }

    //@ assert lseg(h, t, ?ht);
    //@ assert node(t, null, ?tv);
    //@ append_inversion(ht, tv);

    Node prev = head;

    /*@
    if (prev == t) {
      empty_seq(h);
    }
    @*/

    int i = 1;
    while (i < index)
      /*@ invariant 1 <= i &*& i <= index &*& h != null &*& t != null &*& prev != null &*&
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
        if (prev != t) {
          open lseg(nextPrev, _, _);
          open node(nextPrev, _, _);
        }
        assert false;
      }
      @*/
      /*@
      if (nextPrev == t) {
        empty_seq(nextPrev);
        close node(prev, nextPrev, ?pv);
        add_lemma(h, prev, nextPrev);
        length_drop(i, list);
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
      //@ close node(newNode, null, f);
      //@ open node(t, null, tv);
      tail.next = newNode;
      //@ close node(t, newNode, tv);
      //@ add_lemma(h, t, newNode);
      tail = newNode;
      //@ drop_n_plus_one(i - 1, list);
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
    }
  }

  public void reverse()
    //@ requires llist(this, _, _, ?list);
    //@ ensures llist(this, _, _, reverse(list));
  {
    //@ open llist(this, ?h, ?t, list);
    if (head == tail) {
      /*@
      if (head != null) {
        open lseg(h, t, _);
      }
      @*/
      return;
    }
    
    Node oldHead = head;
    Node curr = head;
    Node prev = null;
    while (curr != null)
      /*@ invariant
            (
              prev == null ?
                (
                  curr == null ?
                    false :
                    (
                      oldHead == curr &*&
                      curr != prev &*&
                      lseg(curr, t, ?b) &*& node(t, null, ?tailVal) &*&
                      list == append(b, cons(tailVal, nil)) &*& list != nil
                    )
                ) :
                (
                  curr == null ?
                    (
                      curr != prev &*&
                      lseg(prev, oldHead, ?a) &*& node(oldHead, null, ?oldHeadVal) &*&
                      list == cons(oldHeadVal, reverse(a)) &*& list != nil
                    ) :
                    (
                      curr != prev &*&
                      lseg(prev, oldHead, ?a) &*& node(oldHead, null, ?oldHeadVal) &*&
                      lseg(curr, t, ?b) &*& node(t, null, ?tailVal) &*&
                      list == append(cons(oldHeadVal, reverse(a)), append(b, cons(tailVal, nil))) &*& list != nil
                    )
                )
            );
      @*/
    {
      //@ open lseg(curr, t, ?b);
      //@ open node(curr, ?currNext, ?currVal);
      Node next = curr.next;
      curr.next = prev;
      //@ close node(curr, prev, currVal);
      /*@
      if (curr != t) {
        lseg_start_non_null(currNext, t);
        open lseg(currNext, t, ?tmp);
        distinct_nodes(curr, currNext);
        close lseg(currNext, t, tmp);
      }
      @*/
      /*@
      if (curr == oldHead) {
        if (prev != null) {
          distinct_nodes(curr, oldHead);
          assert false;
        }
      } else {
        assert node(oldHead, null, ?oldHeadVal);
        assert lseg(prev, oldHead, ?a);
        close lseg(curr, oldHead, ?a2);
        if (currNext != null) {
          assert node(t, null, ?tailVal);
          move_node_right_left(oldHeadVal, a, b, tailVal);
        }
      }
      @*/
      prev = curr;
      curr = next;
    }
    head = prev;
    tail = oldHead;
    //@ assert lseg(prev, oldHead, ?l);
    //@ assert node(oldHead, null, ?oldHeadVal);
    //@ append_cons_not_nil(l, oldHeadVal, nil);
  }
}
