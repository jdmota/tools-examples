import edu.cmu.cs.plural.annot.*;

@Similar("p")
@Refine({
  @States(value={"withoutValue"}, refined="alive"),
  @States(value={"withValue"}, refined="alive")
})
@ClassStates({
  @State(name="withoutValue", inv="unique(next) in withValue"),
  @State(name="withValue", inv="unique(next) in withValue * p(value)")
})
class Node<T> {
  @Apply("p")
  private Node<T> next;
  private T value;

  @Perm(ensures="unique(this!fr) in withValue")
  public Node(@PolyVar(value="p", returned=false) T value) {
    this.value = value;
    this.next = null;
  }

  @Unique(requires="alive")
	@ResultUnique(ensures="withValue")
	@ResultApply("p")
  public Node<T> getNext() {
    return this.next;
  }

  @Unique(requires="withValue", ensures="withValue")
  public void setNext(
    @Unique(requires="withValue", returned=false) @Apply("p") Node<T> next
  ) {
    this.next = next;
  }

  @Unique(requires="withValue", ensures="withoutValue")
	@ResultPolyVar("p")
  public T getValue() {
    return this.value;
  }
}

@Similar("p")
@Refine({
  @States(value={"empty", "notEmpty"}, refined="alive")
})
@ClassStates({
  @State(name="empty", inv="head == null * tail == null"),
  @State(
    name="notEmpty",
    inv="unique(head) in withValue * head != null * tail != null"
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

  @Unique(ensures="notEmpty")
  public void add(@PolyVar(value="p", returned=false) T value) {
    @Apply("p") Node<T> n = new Node<>(value);
    if (head == null) {
      head = n;
      tail = n;
    } else {
      tail.setNext(n);
      tail = n;
    }
  }

  @Unique(requires="notEmpty")
  @ResultPolyVar("p")
  public T remove() {
    T result = head.getValue();
    head = head.getNext();
    if (head == null) {
      tail = null;
    }
    return result;
  }
}
