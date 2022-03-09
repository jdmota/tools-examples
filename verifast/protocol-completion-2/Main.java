/*@
predicate_ctor INV(int state)(FileReader f;) = f != null &*& filereader(f, state, _);
@*/

public class Main {

  public static void main(String[] args)
    //@ requires tracker(0);
    //@ ensures tracker(0);
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
    //@ requires list != null &*& llist(list, _, _, ?l) &*& tracker(length(l)) &*& foreachp(l, INV(FileReader.STATE_INIT));
    //@ ensures list != null &*& llist(list, _, _, l) &*& tracker(0) &*& foreachp(l, INV(FileReader.STATE_CLOSED));
  {
    LinkedListIterator it = list.iterator();
    while (it.hasNext())
      /*@ invariant
          it != null &*& iterator(list, it, _, l, ?a, ?b) &*&
          tracker(length(b)) &*&
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

}
