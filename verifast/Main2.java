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

public class Main2 {
  
  public static void main()
    //@ requires true;
    //@ ensures true;
  {
    LinkedList l = new LinkedList();
    Callback c1 = new Callback(l);
    //Callback c2 = new Callback(l);
    c1.run();
    //c2.run();
  }

}
