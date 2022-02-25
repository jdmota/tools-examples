import java.util.concurrent.*;

class Callback implements Runnable {

  private LinkedList list;
  
  //@ predicate pre() = this.list |-> ?l &*& l != null &*& llist(l, _, _, _);
  //@ predicate post() = pre();

  public Callback(LinkedList l)
    //@ requires l != null &*& llist(l, _, _, _);
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

/*@
predicate_ctor CLinkedListState(CLinkedList c)() = c.list |-> ?l &*& l != null &*& llist(l, _, _, _);

predicate CLinkedList(CLinkedList c, real f, real f2, int permits;) = [f]c.lock |-> ?s &*& s != null &*& semaphore_handle(s, CLinkedListState(c), f2, permits);
@*/

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

class Callback2 implements Runnable {

  private CLinkedList list;
  
  //@ predicate pre() = this.list |-> ?l &*& l != null &*& CLinkedList(l, 1/2, 1/3, 0);
  //@ predicate post() = pre();

  public Callback2(CLinkedList l)
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

public class Main2 {

  // Without locks this kind of sharing is not possible
  public static void main1()
    //@ requires true;
    //@ ensures true;
  {
    LinkedList l = new LinkedList();
    Callback c1 = new Callback(l);
    //Callback c2 = new Callback(l);
    c1.run();
    //c2.run();
  }

  // With locks it works
  public static void main2()
    //@ requires true;
    //@ ensures true;
  {
    CLinkedList l = new CLinkedList();
    //@ open CLinkedList(l, 1, 1, 1);
    //@ l.lock.splitHandle(1r, 1, 1r/3, 1);
    //@ l.lock.splitHandle(2r/3, 0, 1r/3, 0);
    //@ close CLinkedList(l, 1/2, 1/3, 0);
    Callback2 c1 = new Callback2(l);
    //@ close CLinkedList(l, 1/2, 1/3, 0);
    Callback2 c2 = new Callback2(l);
    c1.run();
    c2.run();
  }

}
