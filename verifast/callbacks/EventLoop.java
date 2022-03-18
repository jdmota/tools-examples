/*@
predicate holds(predicate() p) = p();

predicate eventloop(EventLoop e, int id, list<predicate()> preds) =
  e.cb1 |-> ?cb1 &*& e.cb2 |-> ?cb2 &*&
  (cb1 == null ? emp : callback(cb1, id, _)) &*& (cb2 == null ? emp : callback(cb2, id, _)) &*&
  strong_ghost_list<predicate()>(id, preds) &*& foreach<predicate()>(preds, holds);

predicate_ctor listCtor(LinkedList l)() = l != null &*& llist(l, _, _, _);

predicate callback(Callback3 cb, int id, LinkedList l) =
  cb.list |-> l &*& [_]strong_ghost_list_member_handle(id, listCtor(l));

lemma void create_eventloop(EventLoop e)
  requires e.cb1 |-> null &*& e.cb2 |-> null;
  ensures eventloop(e, _, nil);
{
  int id = create_strong_ghost_list<predicate()>();
  close foreach(nil, holds);
  close eventloop(e, id, nil);
}
@*/

class Callback3 {

  private LinkedList list;

  public Callback3(LinkedList l)
    //@ requires [_]strong_ghost_list_member_handle(?id, listCtor(l));
    //@ ensures callback(this, id, l);
  {
    this.list = l;
    //@ close callback(this, id, l);
  }

  public void run()
    //@ requires callback(this, ?id, ?l) &*& eventloop(?e, id, ?preds);
    //@ ensures callback(this, id, l) &*& eventloop(e, id, preds);
  {
    //@ open callback(this, id, l);
    //@ open eventloop(e, id, preds);
    //@ strong_ghost_list_member_handle_lemma();
    //@ foreach_remove(listCtor(l), preds);
    //@ open holds(listCtor(l));
    //@ open listCtor(l)();
    this.list.add(new FileReader("file.txt"));
    //@ close listCtor(l)();
    //@ close holds(listCtor(l));
    //@ foreach_unremove(listCtor(l), preds);
    //@ close callback(this, id, l);
    //@ close eventloop(e, id, preds);
  }
}

// A very simple event loop implementation that
// only allows for two callbacks to be queued at the same time
class EventLoop {
  private Callback3 cb1;
  private Callback3 cb2;
  
  public EventLoop()
    //@ requires true;
    //@ ensures eventloop(this, _, nil);
  {
    this.cb1 = null;
    this.cb2 = null;
    //@ create_eventloop(this);
  }
  
  public void addObject(LinkedList l)
    //@ requires eventloop(this, ?id, ?preds) &*& listCtor(l)();
    //@ ensures eventloop(this, id, append(preds, cons(listCtor(l), nil))) &*& strong_ghost_list_member_handle(id, listCtor(l));
  {
    //@ open eventloop(this, id, preds);
    //@ strong_ghost_list_insert(id, preds, nil, listCtor(l));
    //@ close holds(listCtor(l));
    //@ close foreach(nil, holds);
    //@ close foreach(cons(listCtor(l), nil), holds);
    //@ foreach_append(preds, cons(listCtor(l), nil));
    //@ close eventloop(this, id, append(preds, cons(listCtor(l), nil)));
  }
  
  public void addCallback(Callback3 cb)
    //@ requires eventloop(this, ?id, ?preds) &*& callback(cb, id, _);
    //@ ensures eventloop(this, id, preds);
  {
    //@ open eventloop(this, id, preds);
    if (this.cb1 == null) {
      this.cb1 = cb;
    } else if (this.cb2 == null) {
      this.cb2 = cb;
    }
    //@ close eventloop(this, id, preds);
  }
  
  public void runAll()
    //@ requires eventloop(this, ?id, ?preds);
    //@ ensures eventloop(this, id, preds);
  {
    //@ open eventloop(this, id, preds);
    if (this.cb1 != null) {
      Callback3 cb = this.cb1;
      this.cb1 = null;
      //@ close eventloop(this, id, preds);
      cb.run();
      //@ open eventloop(this, id, preds);
    }
    
    if (this.cb2 != null) {
      Callback3 cb = this.cb2;
      this.cb2 = null;
      //@ close eventloop(this, id, preds);
      cb.run();
      //@ open eventloop(this, id, preds);
    }
    //@ close eventloop(this, id, preds);
  }
  
  public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
  {
    LinkedList l = new LinkedList();
    EventLoop e = new EventLoop();
    //@ close listCtor(l)();
    e.addObject(l);
    
    //@ split_fraction strong_ghost_list_member_handle(_, listCtor(l));
    Callback3 c1 = new Callback3(l);
    Callback3 c2 = new Callback3(l);
    e.addCallback(c1);
    e.addCallback(c2);
    
    e.runAll();
  }
}
