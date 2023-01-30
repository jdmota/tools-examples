import edu.cmu.cs.plural.annot.*;

@Similar("p")
@Refine({
  @States(value={"empty", "notEmpty"}, refined="alive")
})
@ClassStates({
  @State(name="empty", inv="head == null * tail == null"),
  @State(
    name="notEmpty",
    inv="unique(head) in withValue,dimNext * head != null * tail != null"
  )
})
public class LinkedList<T> {
  @Apply("p")
  private Node<T> head;
  @Apply("p")
  private Node<T> tail;

  @Perm(ensures="unique(this!fr) in empty")
  public LinkedList() {
    head = null;
    tail = null;
  }

  @Unique(requires="alive", ensures="notEmpty", use=Use.FIELDS)
  public void add(@PolyVar(value="p", returned=false) T value) {
    @Apply("p") Node<T> n = new Node<T>(value);
    if (head == null) {
      head = n;
      tail = n;
    } else {
      tail.setNext(n);
      tail = n;
    }
  }

  @Unique(requires="notEmpty", ensures="alive", use=Use.FIELDS)
  @ResultPolyVar("p")
  public T remove() {
    T result = head.getValue();
    if (head.hasNext()){
      head = head.getNext();
    } else {
      head = null;
      tail = null;
    }
    return result;
  }

  @Imm(guarantee="alive", use=Use.FIELDS)
  @TrueIndicates("empty")
  @FalseIndicates("notEmpty")
  public boolean isEmpty() {
    if (head == null && tail == null) {
      return true;
    }
    return false;
  }
}
