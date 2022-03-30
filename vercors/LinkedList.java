public class LinkedList {
  /*@
  static resource nodes(Node n) =
    n == null ? true : Perm(n.next, 1) ** Perm(n.value, 1) ** nodes(n.next);

  requires [1\2]nodes(n);
  static pure seq<FileReader> nodes_list(Node n) =
    \unfolding [1\2]nodes(n) \in (
      n == null ?
        seq<FileReader> {} :
        seq<FileReader> { n.value } + nodes_list(n.next)
    );

  static resource nodes_until(Node n, Node end) =
    n == end ?
      true :
      n != null ** Perm(n.next, 1) ** Perm(n.value, 1) ** nodes_until(n.next, end);

  requires [1\2]nodes_until(n, end);
  static pure seq<FileReader> nodes_until_list(Node n, Node end) =
    \unfolding [1\2]nodes_until(n, end) \in (
      n == end ?
        seq<FileReader> {} :
        seq<FileReader> { n.value } + nodes_until_list(n.next, end)
    );

  requires [1\2]nodes(n);
  static pure Node get_last(Node n) =
    \unfolding [1\2]nodes(n) \in (n == null || n.next == null ? n : get_last(n.next));

  requires ([1\2]nodes_until(h, t)) ** PointsTo(t.next, 1\2, null) ** Perm(t.value, 1\2);
  requires list == nodes_until_list(h, t) + seq<FileReader> { t.value };
  ensures [1\2]nodes(h);
  ensures list == nodes_list(h);
  ghost static void prepare_iterator(Node h, Node t, seq<FileReader> list) {
    if (h == t) {
      fold [1\2]nodes(h.next);
      fold [1\2]nodes(h);
    } else {
      unfold [1\2]nodes_until(h, t);
      prepare_iterator(h.next, t, tail(list));
      fold [1\2]nodes(h);
    }
  }

  requires ([1\2]nodes_until(h, t)) ** PointsTo(t.next, 1\2, null) ** Perm(t.value, 1\2);
  requires list == nodes_until_list(h, t) + seq<FileReader> { t.value };
  requires [1\2]nodes_until(h, null);
  requires list == nodes_until_list(h, null);
  ensures nodes_until(h, t) ** PointsTo(t.next, 1, null) ** Perm(t.value, 1);
  ensures list == nodes_until_list(h, t) + seq<FileReader> { t.value };
  ghost static void dispose_iterator(Node h, Node t, seq<FileReader> list) {
    if (h == t) {
      unfold [1\2]nodes_until(h, t);
      unfold [1\2]nodes_until(h, null);
      fold nodes_until(h, t);
    } else {
      unfold [1\2]nodes_until(h, t);
      unfold [1\2]nodes_until(h, null);
      dispose_iterator(h.next, t, tail(list));
      fold nodes_until(h, t);
    }
  }
  @*/

  /*@
  final resource state(seq<FileReader> list) =
    Perm(h, 1) ** Perm(t, 1) **
    (
      h == null ? (t == null ** list == seq<FileReader> {}) :
        (
          t == null ? (h == null ** list == seq<FileReader> {}) :
            (
              nodes_until(h, t) ** PointsTo(t.next, 1, null) ** Perm(t.value, 1) **
              list == (nodes_until_list(h, t) + seq<FileReader> { t.value })
            )
        )
    );
  @*/

  /*@
  requires n1 != null ** n2 != null ** n3 != null;
  requires nodes_until(n1, n2) ** Perm(n2.next, 1) ** Perm(n2.value, 1) ** n2.next == n3 ** PointsTo(n3.next, 1, null);
  requires list == nodes_until_list(n1, n2) + seq<FileReader> { n2.value };
  ensures nodes_until(n1, n3) ** PointsTo(n3.next, 1, null) ** list == nodes_until_list(n1, n3);
  ghost static void add_lemma(Node n1, Node n2, Node n3, seq<FileReader> list) {
    if (n1 == n2) {
      unfold nodes_until(n1, n2);
      fold nodes_until(n3, n3);
      fold nodes_until(n1, n3);
    } else {
      unfold nodes_until(n1, n2);
      unfold nodes_until(n1.next, n2);
      assert n1.next != null;
      fold nodes_until(n1.next, n2);
      add_lemma(n1.next, n2, n3, tail(list));
      fold nodes_until(n1, n3);
    }
  }
  @*/

  /*@
  requires n2 != null;
  requires ([1\2]nodes_until(n1, n2)) ** PointsTo(n2.next, 1\2, n3) ** PointsTo(n2.value, 1\2, value);
  requires [1\2]nodes(n3);
  requires seen == nodes_until_list(n1, n2);
  requires remaining == seq<FileReader> { value } + nodes_list(n3);
  requires ([1\4]nodes_until(n1, t)) ** PointsTo(t.next, 1\4, null) ** Perm(t.value, 1\4);
  ensures [1\2]nodes_until(n1, n3);
  ensures [1\2]nodes(n3);
  ensures seen + seq<FileReader> { value } == nodes_until_list(n1, n3);
  ensures remaining == seq<FileReader> { value } + nodes_list(n3);
  ensures ([1\4]nodes_until(n1, t)) ** PointsTo(t.next, 1\4, null) ** Perm(t.value, 1\4);
  ghost static void advance(seq<FileReader> seen, seq<FileReader> remaining, Node n1, Node n2, Node n3, FileReader value, Node t) {
    if (n1 == n2) {
      unfold [1\2]nodes_until(n1, n2);
      unfold [1\2]nodes(n3);
      unfold [1\4]nodes_until(n1, t);
      fold [1\2]nodes_until(n3, n3);
      assert n1 != n3;
      fold [1\2]nodes_until(n1, n3);
      fold [1\2]nodes(n3);
      fold [1\4]nodes_until(n1, t);
    } else {
      if (n1 == t) {
        unfold [1\2]nodes_until(n1, n2);
        unfold [1\2]nodes_until(n1.next, n2);
        unfold [1\4]nodes_until(n1, t);
        assert n1.next == null;
        assert false;
      } else {
        unfold [1\2]nodes_until(n1, n2);
        unfold [1\2]nodes(n3);
        unfold [1\4]nodes_until(n1, t);
        assert n1 != n3;
        fold [1\2]nodes(n3);
        advance(tail(seen), remaining, n1.next, n2, n3, value, t);
        fold [1\2]nodes_until(n1, n3);
        fold [1\4]nodes_until(n1, t);
      }
    }
  }
  @*/

  private Node h;
  private Node t;
  
  //@ yields seq<FileReader> newList;
  //@ requires true;
  //@ ensures state(newList) ** newList == seq<FileReader> {};
  public LinkedList() {
    h = null;
    t = null;
    //@ ghost newList = seq<FileReader> {};
    //@ fold state(newList);
  }

  //@ given seq<FileReader> oldList;
  //@ yields seq<FileReader> newList;
  //@ requires state(oldList);
  //@ ensures state(newList) ** newList == oldList + seq<FileReader> { x };
  public void add(FileReader x) {
    //@ unfold state(oldList);
    Node n = new Node();
    n.value = x;
    n.next = null;
    if (h == null) {
      h = n;
      t = n;
      //@ ghost newList = oldList + seq<FileReader> { x };
      //@ fold nodes_until(h, t);
      //@ fold state(newList);
    } else {
      t.next = n;
      //@ ghost add_lemma(h, t, n, oldList);
      t = n;
      //@ ghost newList = oldList + seq<FileReader> { x };
      //@ assert newList == nodes_until_list(h, t) + seq<FileReader> { t.value };
      //@ fold state(newList);
    }
  }
  
  //@ given seq<FileReader> oldList;
  //@ yields seq<FileReader> newList;
  //@ requires state(oldList) ** |oldList| > 0;
  //@ ensures state(newList) ** newList == tail(oldList);
  public FileReader remove() {
    //@ unfold state(oldList);
    //@ unfold nodes_until(h, t);
    FileReader result = h.value;
    if (h == t) {
      h = null;
      t = null;
      //@ ghost newList = tail(oldList);
      //@ fold state(newList);
    } else {
      //@ assert nodes_until(h.next, t);
      //@ unfold nodes_until(h.next, t);
      //@ assert h.next != null;
      //@ fold nodes_until(h.next, t);
      h = h.next;
      //@ assert nodes_until(h, t);
      //@ ghost newList = tail(oldList);
      //@ fold state(newList);
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

  //@ given seq<FileReader> list;
  //@ requires state(list);
  //@ ensures \result.state(this, seq<FileReader> {}, list);
  public LinkedListIterator iterator() {
    //@ unfold state(list);
    /*@ ghost if (h == null) {
      fold [1\2]nodes(h);
    } else {
      prepare_iterator(h, t, list);
    }
    @*/
    //@ fold [1\2]state(list);
    return new LinkedListIterator(h) /*@ with {linkedlist=this; list=list;} @*/;
  }
}
