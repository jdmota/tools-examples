/*@
predicate_ctor INV(int state)(FileReader f) = f != null &*& filereader(f, state, _);
@*/

public class Main {

  public static void main(String[] args)
    //@ requires true;
    //@ ensures tracker(nil);
  {
    FileReadersTracker t = new FileReadersTracker();
    LinkedList list = new LinkedList();
    FileReader f1 = t.newFileReader("a");
    FileReader f2 = t.newFileReader("b");
    FileReader f3 = t.newFileReader("c");
    list.add(f1);
    list.add(f2);
    list.add(f3);
    //@ close INV(FileReader.STATE_INIT)(f1);
    //@ close INV(FileReader.STATE_INIT)(f2);
    //@ close INV(FileReader.STATE_INIT)(f3);
    //@ assert llist(list, _, _, ?l);
    //@ close foreach(nil, INV(FileReader.STATE_INIT));
    //@ close foreach(cons(f3, nil), INV(FileReader.STATE_INIT));
    //@ close foreach(cons(f2, cons(f3, nil)), INV(FileReader.STATE_INIT));
    //@ close foreach(l, INV(FileReader.STATE_INIT));
    useFiles(list);
    //@ open foreach(l, INV(FileReader.STATE_CLOSED));
    //@ open foreach(cons(f2, cons(f3, nil)), INV(FileReader.STATE_CLOSED));
    //@ open foreach(cons(f3, nil), INV(FileReader.STATE_CLOSED));
    //@ open INV(FileReader.STATE_CLOSED)(f1);
    //@ open INV(FileReader.STATE_CLOSED)(f2);
    //@ open INV(FileReader.STATE_CLOSED)(f3);
    t.dropFileReader(f1);
    t.dropFileReader(f2);
    t.dropFileReader(f3);
  }
  
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
    //@ close INV(FileReader.STATE_INIT)(f1);
    //@ close INV(FileReader.STATE_INIT)(f2);
    //@ close INV(FileReader.STATE_INIT)(f3);
    //@ assert llist(list, _, _, ?l);
    //@ close foreach(nil, INV(FileReader.STATE_INIT));
    //@ close foreach(cons(f3, nil), INV(FileReader.STATE_INIT));
    //@ close foreach(cons(f2, cons(f3, nil)), INV(FileReader.STATE_INIT));
    //@ close foreach(l, INV(FileReader.STATE_INIT));
    useFiles(list);
  }
  
  public static void useFiles(LinkedList list)
    //@ requires list != null &*& llist(list, _, _, ?l) &*& foreach(l, INV(FileReader.STATE_INIT));
    //@ ensures list != null &*& llist(list, _, _, l) &*& foreach(l, INV(FileReader.STATE_CLOSED));
  {
    //@ close foreach(nil, INV(FileReader.STATE_CLOSED));
    LinkedListIterator it = list.iterator();
    while (it.hasNext())
      /*@ invariant it != null &*& iterator(list, it, _, l, ?a, ?b) &*&
          foreach(a, INV(FileReader.STATE_CLOSED)) &*&
          foreach(b, INV(FileReader.STATE_INIT));
       @*/
    {
      FileReader f = it.next();
      //@ open foreach(b, _);
      //@ open INV(FileReader.STATE_INIT)(f);
      f.open();
      while (!f.eof())
      //@ invariant f != null &*& filereader(f, FileReader.STATE_OPENED, _);
      {
        //@ open filereader(f, _, _);
        f.read();
      }
      f.close();
      //@ close INV(FileReader.STATE_CLOSED)(f);
      //@ close foreach(nil, INV(FileReader.STATE_CLOSED));
      //@ close foreach(cons(f, nil), INV(FileReader.STATE_CLOSED));
      //@ foreach_append(a, cons(f, nil));
    }
    //@ dispose_iterator(it);
  }

}
