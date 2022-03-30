public class LinkedList {
  /*@
  final resource state(seq<FileReader> l) =
    Perm(h, 1) ** Perm(t, 1) ** Perm(list, 1) ** l == list **
    (
      h == null ? (t == null ** list == seq<FileReader> {}) :
        (
          t == null ? (h == null ** list == seq<FileReader> {}) :
            (
              h.seg(t) ** Perm(t.next, 1) ** Perm(t.value, 1) **
              list == (h.segment(t) + seq<FileReader> { t.value })
            )
        )
    );
  @*/

  /*@
  requires n1 != null ** n2 != null ** n3 != null;
  requires n1.seg(n2) ** Perm(n2.next, 1) ** Perm(n2.value, 1) ** n2.next == n3 ** Perm(n3.next, 1);
  requires list == n1.segment(n2) + seq<FileReader> { n2.value };
  ensures n1.seg(n3) ** Perm(n3.next, 1) ** list == n1.segment(n3);
  ghost static void add_lemma(Node n1, Node n2, Node n3, seq<FileReader> list) {
    if (n1 == n2) {
      unfold n1.seg(n2);
      fold n3.seg(n3);
      fold n2.seg(n3);
    } else {
      unfold n1.seg(n2);
      add_lemma(n1.next, n2, n3, tail(list));
      fold n1.seg(n3);
    }
  }
  @*/

  //@ ghost private seq<FileReader> list;
  private Node h;
  private Node t;
  
  //@ requires true;
  //@ ensures state(seq<FileReader> {});
  public LinkedList() {
    h = null;
    t = null;
    //@ ghost list = seq<FileReader> {};
    //@ fold state(list);
  }

  //@ given seq<FileReader> oldList;
  //@ requires state(oldList);
  //@ ensures state(oldList + seq<FileReader> { x });
  public void add(FileReader x) {
    //@ unfold state(oldList);
    Node n = new Node();
    n.value = x;
    n.next = null;
    if (h == null) {
      h = n;
      t = n;
      //@ ghost list = list + seq<FileReader> { x };
      //@ fold h.seg(t);
      //@ fold state(list);
    } else {
      t.next = n;
      //@ ghost add_lemma(h, t, n, list);
      t = n;
      //@ ghost list = list + seq<FileReader> { x };
      //@ assert list == h.segment(t) + seq<FileReader> { t.value };
      //@ fold state(list);
    }
  }
  
  //@ given seq<FileReader> oldList;
  //@ requires state(oldList) ** |oldList| > 0;
  //@ ensures state(tail(oldList));
  public FileReader remove() {
    //@ unfold state(oldList);
    //@ unfold h.seg(t);
    FileReader result = h.value;
    if (h == t) {
      h = null;
      t = null;
      //@ ghost list = tail(list);
      //@ fold state(list);
    } else {
      //@ assert h.next.seg(t);
      h = h.next;
      //@ assert h.seg(t);
      //@ ghost list = tail(list);
      //@ fold state(list);
    }
    return result;
  }

  //@ given seq<FileReader> oldList;
  //@ requires state(oldList);
  //@ ensures state(oldList) ** \result == |oldList| > 0;
  public boolean notEmpty() {
    //@ unfold state(oldList);
    boolean r = h != null;
    //@ fold state(oldList);
    return r;
  }

  /*
  // requires llist(this, ?h, _, ?list);
  // ensures iterator(this, result, h, list, nil, list) &*& result != null;
  public LinkedListIterator iterator() {
    return new LinkedListIterator(this, h);
  }*/
}
