public class Main {
  //@ given FileTracker tracker;
  //@ context Perm(tracker.active, 1);
  //@ requires tracker.active == 0;
  //@ ensures tracker.active == 0;
  public static void main(String[] args) {
    //@ ghost seq<FileReader> l;
    LinkedList list = new LinkedList() /*@ then {l=newList;} @*/;
    FileReader f1 = new FileReader() /*@ with {tracker=tracker;} @*/;
    FileReader f2 = new FileReader() /*@ with {tracker=tracker;} @*/;
    FileReader f3 = new FileReader() /*@ with {tracker=tracker;} @*/;
    //@ assert f1 != f2 && f2 != f3 && f1 != f3;
    //@ fold filereader(f1, 1);
    //@ fold filereader(f2, 1);
    //@ fold filereader(f3, 1);
    list.add(f1) /*@ with {oldList=l;} then {l=newList;} @*/;
    list.add(f2) /*@ with {oldList=l;} then {l=newList;} @*/;
    list.add(f3) /*@ with {oldList=l;} then {l=newList;} @*/;
    //@ assert l == seq<FileReader> {f1, f2, f3};
    //@ assert |l| == 3;
    //@ assert (\forall* int i; i >= 0 && i < |l|; filereader(l[i], 1));
    useFiles(list) /*@ with {tracker=tracker; l=l;} @*/;
  }

  /*@
  static resource filereader(FileReader f, int state) =
    PointsTo(f.state, 1, state) ** Perm(f.remaining, 1) ** f.remaining >= 0;
  @*/
  
  //@ given FileTracker tracker;
  //@ given seq<FileReader> l;
  //@ context_everywhere Perm(tracker.active, 1);
  //@ requires tracker.active == |l|;
  //@ ensures tracker.active == 0;
  //@ context linkedlist != null ** linkedlist.state(l);
  //@ requires (\forall* int i; i >= 0 && i < |l|; filereader(l[i], 1));
  //@ ensures (\forall* int i; i >= 0 && i < |l|; filereader(l[i], 3));
  public static void useFiles(LinkedList linkedlist) {
    //@ ghost seq<FileReader> seen = seq<FileReader> {};
    //@ ghost seq<FileReader> remaining = l;
    LinkedListIterator it = linkedlist.iterator() /*@ with {list=l;} @*/;
    //@ assert it.state(linkedlist, seen, remaining);
    boolean has = it.hasNext() /*@ with {linkedlist=linkedlist; s=seen; r=remaining;} @*/;
    //@ loop_invariant it != null ** it.state(linkedlist, seen, remaining) ** seen + remaining == l;
    //@ loop_invariant tracker.active == |remaining|;
    //@ loop_invariant has == (|remaining| > 0);
    //@ loop_invariant (\forall* int i; i >= 0 && i < |seen|; filereader(seen[i], 3));
    //@ loop_invariant (\forall* int i; i >= 0 && i < |remaining|; filereader(remaining[i], 1));
    while (has) {
      FileReader f = it.next() /*@ with {linkedlist=linkedlist; s=seen; r=remaining;} @*/;
      //@ ghost seen = seen + seq<FileReader> { f };
      //@ ghost remaining = tail(remaining);
      //@ unfold filereader(f, 1);
      f.open();
      // Workaround https://github.com/utwente-fmt/vercors/issues/436
      boolean end = f.eof();
      //@ loop_invariant Perm(f.state, 1) ** Perm(f.remaining, 1) ** f.state == 2 ** f.remaining >= 0 ** (end == (f.remaining == 0));
      //@ loop_invariant tracker.active == |remaining| + 1;
      while (!end) {
        f.read();
        end = f.eof();
      }
      f.close() /*@ with {tracker=tracker;} @*/;
      //@ fold filereader(f, 3);
      has = it.hasNext() /*@ with {linkedlist=linkedlist; s=seen; r=remaining;} @*/;
    }
    it.dispose() /*@ with {linkedlist=linkedlist; list=seen;} @*/;
  }
}
