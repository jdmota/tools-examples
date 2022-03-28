public class LinkedList {
  /*@
  final resource state() =
    Perm(h, 1) ** Perm(t, 1) **
      (h == null ? t == null :
      (t == null ? h == null :
      h.seg(t) ** Perm(t.next, 1) ** Perm(t.value, 1)));
  @*/

  /*@
  requires n1 != null ** n2 != null ** n3 != null;
  requires n1.seg(n2) ** Perm(n2.next, 1) ** Perm(n2.value, 1) ** n2.next == n3 ** Perm(n3.next, 1) ** Perm(n3.value, 1);
  ensures n1.seg(n3) ** Perm(n3.next, 1) ** Perm(n3.value, 1);
  ghost static void add_lemma(Node n1, Node n2, Node n3) {
    if (n1 == n2) {
      unfold n1.seg(n2);
      fold n3.seg(n3);
      fold n2.seg(n3);
    } else {
      unfold n1.seg(n2);
      add_lemma(n1.next, n2, n3);
      fold n1.seg(n3);
    }
  }
  @*/

  private Node h;
  private Node t;
  
  //@ requires true;
  //@ ensures state();
  public LinkedList() {
    h = null;
    t = null;
    //@ fold state();
  }
  
  //@ requires state();
  //@ ensures state();
  public void add(FileReader x) {
    //@ unfold state();
    Node n = new Node();
    n.value = x;
    n.next = null;
    if (h == null) {
      h = n;
      t = n;
      //@ fold h.seg(t);
      //@ fold state();
    } else {
      t.next = n;
      //@ ghost add_lemma(h, t, n);
      t = n;
      //@ fold state();
    }
  }
  
  //@ requires state() ** \unfolding state() \in h != null;
  //@ ensures state();
  public FileReader remove() {
    //@ unfold state();
    //@ unfold h.seg(t);
    FileReader result = h.value;
    if (h == t) {
      h = null;
      t = null;
      //@ fold state();
    } else {
      //@ assert h.next.seg(t);
      h = h.next;
      //@ assert h.seg(t);
      //@ fold state();
    }
    return result;
  }
  
  //@ requires state();
  //@ ensures state();
  public boolean notEmpty() {
    //@ unfold state();
    boolean r = h != null;
    //@ fold state();
    return r;
  }

  /*
  // requires llist(this, ?h, _, ?list);
  // ensures iterator(this, result, h, list, nil, list) &*& result != null;
  public LinkedListIterator iterator() {
    return new LinkedListIterator(this, h);
  }*/
}
