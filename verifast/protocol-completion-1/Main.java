/*@
predicate_ctor INV(int state)(FileReader f;) = f != null &*& filereader(f, state, _);
@*/

public class Main {

  public static void main(String[] args)
    //@ requires true;
    //@ ensures tracker_list(nil);
  {
    FileReadersTracker t = new FileReadersTracker();
    LinkedList list = new LinkedList();
    FileReader f1 = t.newFileReader("a");
    FileReader f2 = t.newFileReader("b");
    FileReader f3 = t.newFileReader("c");
    list.add(f1);
    list.add(f2);
    list.add(f3);
    //@ assert llist(list, _, _, ?l);
    //@ close foreachp(cons(f3, nil), INV(FileReader.STATE_INIT));
    //@ close foreachp(cons(f2, cons(f3, nil)), INV(FileReader.STATE_INIT));
    //@ close foreachp(l, INV(FileReader.STATE_INIT));
    useFiles(list);
    //@ open foreachp(l, INV(FileReader.STATE_CLOSED));
    //@ open foreachp(cons(f2, cons(f3, nil)), INV(FileReader.STATE_CLOSED));
    //@ open foreachp(cons(f3, nil), INV(FileReader.STATE_CLOSED));
    t.dropFileReader(f1);
    t.dropFileReader(f2);
    t.dropFileReader(f3);
  }
  
  // Same as "main", but the FileReadersTracker is not used
  public static void main2(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    LinkedList list = new LinkedList();
    FileReader f1 = new FileReader("a");
    FileReader f2 = new FileReader("b");
    FileReader f3 = new FileReader("c");
    list.add(f1);
    list.add(f2);
    list.add(f3);
    //@ assert llist(list, _, _, ?l);
    //@ close foreachp(cons(f3, nil), INV(FileReader.STATE_INIT));
    //@ close foreachp(cons(f2, cons(f3, nil)), INV(FileReader.STATE_INIT));
    //@ close foreachp(l, INV(FileReader.STATE_INIT));
    useFiles(list);
  }
  
  public static void useFiles(LinkedList list)
    //@ requires list != null &*& llist(list, _, _, ?l) &*& foreachp(l, INV(FileReader.STATE_INIT));
    //@ ensures list != null &*& llist(list, _, _, l) &*& foreachp(l, INV(FileReader.STATE_CLOSED));
  {
    LinkedListIterator it = list.iterator();
    while (it.hasNext())
      /*@ invariant it != null &*& iterator(list, it, _, l, ?a, ?b) &*&
          foreachp(a, INV(FileReader.STATE_CLOSED)) &*&
          foreachp(b, INV(FileReader.STATE_INIT));
       @*/
    {
      FileReader f = it.next();
      //@ open foreachp(b, _);
      //@ open INV(FileReader.STATE_INIT)(f);
      f.open();
      while (!f.eof())
        //@ invariant f != null &*& filereader(f, FileReader.STATE_OPENED, _);
      {
        //@ open filereader(f, _, _);
        f.read();
      }
      f.close();
      //@ close foreachp(nil, INV(FileReader.STATE_CLOSED));
      //@ close foreachp(cons(f, nil), INV(FileReader.STATE_CLOSED));
      //@ foreachp_append(a, cons(f, nil));
    }
    //@ dispose_iterator(it);
  }

  // Notice how we can arbitrarily say we completed the protocol while in fact we did not
  // This code is accepted by VeriFast
  public static void wrongMain(String[] args)
    //@ requires true;
    //@ ensures tracker_list(nil);
  {
    FileReadersTracker t = new FileReadersTracker();
    FileReader f = t.newFileReader("file");
    //@ close tracker_list(nil);
  }

}
