import java.util.concurrent.*;

/*@
predicate_ctor CLinkedListState(CLinkedList c)() = c.list |-> ?l &*& l != null &*& llist(l, _, _, _);

predicate CLinkedList(CLinkedList c, real f, real f2, int permits;) = [f]c.lock |-> ?s &*& s != null &*& semaphore_handle(s, CLinkedListState(c), f2, permits);
@*/

// A concurrent linked-list that uses a lock to acquire exclusive access to the underlying linked-list
class CLinkedList {

  LinkedList list;
  Semaphore lock;
  
  CLinkedList()
    //@ requires true;
    //@ ensures CLinkedList(this, 1, 1, 1);
  {
    list = new LinkedList();
    //@ close CLinkedListState(this)();
    //@ one_time(CLinkedListState(this));
    lock = new Semaphore(1);
    //@ close CLinkedList(this, 1, 1, 1);
  }

  void add(FileReader x)
    //@ requires CLinkedList(this, 1/2, 1/3, 0);
    //@ ensures CLinkedList(this, 1/2, 1/3, 0);
  {
    lock.acquire();
    //@ open CLinkedListState(this)();
    list.add(x);
    //@ close CLinkedListState(this)();
    lock.release();
  }
}

// A callback that uses a concurrent linked-list to add elements to it
// The concurrent linked-list uses a lock to acquire exclusive access to the underlying linked-list
class CCallback implements Runnable {

  private CLinkedList list;
  
  //@ predicate pre() = this.list |-> ?l &*& l != null &*& CLinkedList(l, 1/2, 1/3, 0);
  //@ predicate post() = pre();

  public CCallback(CLinkedList l)
    //@ requires l != null &*& CLinkedList(l, 1/2, 1/3, 0);
    //@ ensures pre();
  {
    this.list = l;
  }

  public void run()
    //@ requires pre();
    //@ ensures post();
  {
    this.list.add(new FileReader("file.txt"));
  }
}

public class CallbackWithLocks {

  // By using locks, this kind of sharing is accepted by Verifast
  // but locks here are unnecessary, given that we are in a single-threaded context
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    CLinkedList l = new CLinkedList();
    //@ open CLinkedList(l, 1, 1, 1);
    //@ l.lock.splitHandle(1r, 1, 1r/3, 1);
    //@ l.lock.splitHandle(2r/3, 0, 1r/3, 0);
    //@ close CLinkedList(l, 1/2, 1/3, 0);
    CCallback c1 = new CCallback(l);
    //@ close CLinkedList(l, 1/2, 1/3, 0);
    CCallback c2 = new CCallback(l);
    c1.run();
    c2.run();
  }

}
