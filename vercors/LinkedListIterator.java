public class LinkedListIterator {
  //@ ghost private Node first;
  //@ ghost private Node last;
  private Node curr;
  
  /*@
  final resource state(LinkedList linkedlist, seq<FileReader> s, seq<FileReader> r) =
    Perm(first, 1) ** Perm(last, 1) ** Perm(curr, 1) **
    Perm(linkedlist.hd, 1\2) ** Perm(linkedlist.tl, 1\2) **
    ([1\2]linkedlist.state(s + r)) **
    ([1\2]LinkedList.nodes_until(first, curr)) **
    ([1\2]LinkedList.nodes(curr)) **
    s == LinkedList.nodes_until_list(first, curr) **
    r == LinkedList.nodes_list(curr) **
    (\unfolding [1\2]linkedlist.state(s + r) \in (first == linkedlist.hd ** last == linkedlist.tl));
  @*/

  //@ given LinkedList linkedlist;
  //@ given seq<FileReader> list;
  //@ requires Perm(linkedlist.hd, 1\2) ** Perm(linkedlist.tl, 1\2);
  //@ requires [1\2]linkedlist.state(list);
  //@ requires ([1\2]LinkedList.nodes(hd)) ** list == LinkedList.nodes_list(hd);
  //@ requires \unfolding [1\2]linkedlist.state(list) \in linkedlist.hd == hd;
  //@ ensures state(linkedlist, seq<FileReader> {}, list);
  public LinkedListIterator(Node hd) {
    //@ unfold [1\2]linkedlist.state(list);
    //@ ghost this.first = hd;
    //@ ghost this.last = linkedlist.tl;
    //@ fold [1\2]linkedlist.state(list);
    curr = hd;
    //@ fold [1\2]LinkedList.nodes_until(first, curr);
    //@ fold state(linkedlist, seq<FileReader> {}, LinkedList.nodes_list(hd));
  }
  
  //@ given LinkedList linkedlist;
  //@ given seq<FileReader> list;
  //@ requires state(linkedlist, list, seq<FileReader> {});
  //@ ensures linkedlist.state(list);
  public void dispose() {
    //@ unfold state(linkedlist, list, seq<FileReader> {});
    //@ unfold [1\2]linkedlist.state(list);
    /*@
    ghost if (linkedlist.hd == null) {
      fold linkedlist.state(list);
    } else {
      LinkedList.dispose_iterator(linkedlist.hd, linkedlist.tl, list);
      fold linkedlist.state(list);
    }
    @*/
  }

  //@ given LinkedList linkedlist;
  //@ given seq<FileReader> s;
  //@ given seq<FileReader> r;
  //@ requires state(linkedlist, s, r);
  //@ ensures state(linkedlist, s, r) ** \result == |r| > 0;
  public boolean hasNext() {
    //@ unfold state(linkedlist, s, r);
    boolean has = curr != null;
    //@ fold state(linkedlist, s, r);
    return has;
  }

  //@ given LinkedList linkedlist;
  //@ given seq<FileReader> s;
  //@ given seq<FileReader> r;
  //@ requires state(linkedlist, s, r) ** |r| > 0;
  //@ ensures state(linkedlist, s + seq<FileReader> { \result }, tail(r)) ** \result == head(r);
  public FileReader next() {
    //@ unfold state(linkedlist, s, r);
    //@ unfold [1\2]linkedlist.state(s + r);
    //@ unfold [1\2]LinkedList.nodes(curr);
    FileReader f = curr.value;
    //@ ghost Node oldCurr = curr;
    //@ ghost Node oldCurrNext = curr.next;
    curr = curr.next;
    //@ ghost LinkedList.advance(s, r, first, oldCurr, oldCurrNext, f, last);
    //@ fold [1\2]linkedlist.state(s + r);
    //@ assert head(r) == f;
    //@ assert s + r == s + seq<FileReader> { f } + tail(r);
    //@ fold state(linkedlist, s + seq<FileReader> { f }, tail(r));
    return f;
  }
}
