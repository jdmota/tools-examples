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

  requires ([1\2]nodes_until(hd, tl)) ** PointsTo(tl.next, 1\2, null) ** Perm(tl.value, 1\2);
  requires list == nodes_until_list(hd, tl) + seq<FileReader> { tl.value };
  ensures [1\2]nodes(hd);
  ensures list == nodes_list(hd);
  ghost static void prepare_iterator(Node hd, Node tl, seq<FileReader> list) {
    if (hd == tl) {
      fold [1\2]nodes(hd.next);
      fold [1\2]nodes(hd);
    } else {
      unfold [1\2]nodes_until(hd, tl);
      prepare_iterator(hd.next, tl, tail(list));
      fold [1\2]nodes(hd);
    }
  }

  requires ([1\2]nodes_until(hd, tl)) ** PointsTo(tl.next, 1\2, null) ** Perm(tl.value, 1\2);
  requires list == nodes_until_list(hd, tl) + seq<FileReader> { tl.value };
  requires [1\2]nodes_until(hd, null);
  requires list == nodes_until_list(hd, null);
  ensures nodes_until(hd, tl) ** PointsTo(tl.next, 1, null) ** Perm(tl.value, 1);
  ensures list == nodes_until_list(hd, tl) + seq<FileReader> { tl.value };
  ghost static void dispose_iterator(Node hd, Node tl, seq<FileReader> list) {
    if (hd == tl) {
      unfold [1\2]nodes_until(hd, tl);
      unfold [1\2]nodes_until(hd, null);
      fold nodes_until(hd, tl);
    } else {
      unfold [1\2]nodes_until(hd, tl);
      unfold [1\2]nodes_until(hd, null);
      dispose_iterator(hd.next, tl, tail(list));
      fold nodes_until(hd, tl);
    }
  }
  @*/

  /*@
  final resource state(seq<FileReader> list) =
    Perm(hd, 1) ** Perm(tl, 1) **
    (
      hd == null ? (tl == null ** list == seq<FileReader> {}) :
        (
          tl == null ? (hd == null ** list == seq<FileReader> {}) :
            (
              nodes_until(hd, tl) ** PointsTo(tl.next, 1, null) ** Perm(tl.value, 1) **
              list == (nodes_until_list(hd, tl) + seq<FileReader> { tl.value })
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

  private Node hd;
  private Node tl;
  
  //@ yields seq<FileReader> newList;
  //@ requires true;
  //@ ensures state(newList) ** newList == seq<FileReader> {};
  public LinkedList() {
    hd = null;
    tl = null;
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
    if (hd == null) {
      hd = n;
      tl = n;
      //@ ghost newList = oldList + seq<FileReader> { x };
      //@ fold nodes_until(hd, tl);
      //@ fold state(newList);
    } else {
      tl.next = n;
      //@ ghost add_lemma(hd, tl, n, oldList);
      tl = n;
      //@ ghost newList = oldList + seq<FileReader> { x };
      //@ assert newList == nodes_until_list(hd, tl) + seq<FileReader> { tl.value };
      //@ fold state(newList);
    }
  }
  
  //@ given seq<FileReader> oldList;
  //@ yields seq<FileReader> newList;
  //@ requires state(oldList) ** |oldList| > 0;
  //@ ensures state(newList) ** newList == tail(oldList);
  public FileReader remove() {
    //@ unfold state(oldList);
    //@ unfold nodes_until(hd, tl);
    FileReader result = hd.value;
    if (hd == tl) {
      hd = null;
      tl = null;
      //@ ghost newList = tail(oldList);
      //@ fold state(newList);
    } else {
      //@ assert nodes_until(hd.next, tl);
      //@ unfold nodes_until(hd.next, tl);
      //@ assert hd.next != null;
      //@ fold nodes_until(hd.next, tl);
      hd = hd.next;
      //@ assert nodes_until(hd, tl);
      //@ ghost newList = tail(oldList);
      //@ fold state(newList);
    }
    return result;
  }

  //@ given seq<FileReader> oldList;
  //@ requires state(oldList);
  //@ ensures state(oldList) ** \result == (|oldList| == 0);
  public boolean isEmpty() {
    //@ unfold state(oldList);
    boolean r = hd == null;
    //@ fold state(oldList);
    return r;
  }

  //@ given seq<FileReader> list;
  //@ requires state(list);
  //@ ensures \result != null ** \result.state(this, seq<FileReader> {}, list);
  public LinkedListIterator iterator() {
    //@ unfold state(list);
    /*@ ghost if (hd == null) {
      fold [1\2]nodes(hd);
    } else {
      prepare_iterator(hd, tl, list);
    }
    @*/
    //@ fold [1\2]state(list);
    return new LinkedListIterator(hd) /*@ with {linkedlist=this; list=list;} @*/;
  }
}
