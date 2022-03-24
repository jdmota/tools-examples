import edu.cmu.cs.plural.annot.Perm;
import edu.cmu.cs.plural.annot.States;

@States(value={"withNext", "withoutNext"}, refine="alive")
@ClassStates({
  @State(name="withNext", inv="pure(value) * unique(next)"),
  @State(name="withoutNext", inv="pure(value) * none(next)")
})
class Node<T> {
  private T value;
  private Node<T> next;

  @Perm(requires="pure(value)", ensures="unique(this) in withoutNext")
  public Node(T value) {
    this.value = value;
    this.next = null;
  }

  @Perm(
    requires="unique(this) in withNext",
    ensures="unique(this) in withoutNext * unique(result)"
  )
  public Node<T> getNext() {
    return this.next;
  }

  @Perm(
    requires="unique(this) in withoutNext * unique(next)",
    ensures="unique(this) in withNext"
  )
  public void setNext(Node<T> next) {
    this.next = next;
  }

  @Perm(requires="pure(this)", ensures="pure(this) * pure(result)")
  public T getValue() {
    return this.value;
  }
}

@States(value={"empty", "notEmpty"}, refine="alive")
@ClassStates({
  @State(name="empty", inv="head == null * tail == null"),
  @State(
    name="notEmpty",
    inv="unique(head) in withNext * head != null * tail != null"
  )
})
public class LinkedList<T> {
  private Node<T> head;
  private Node<T> tail;

  @Perm(requires="one", ensures="unique(this) in empty")
  public LinkedList() {
    head = null;
    tail = null;
  }

  @Perm(requires="full(this) * pure(element)", ensures="full(this) in notEmpty")
  public void add(T element) {
    Node<T> n = new Node<>(element);
    if (head == null) {
      head = n;
      tail = n;
    } else {
      tail.setNext(n);
      tail = n;
    }
  }

  @Perm(requires="full(this) in notEmpty", ensures="full(this) * pure(result)")
  public T remove() {
    T result = head.getValue();
    head = head.getNext();
    if (head == null) {
      tail = null;
    }
    return result;
  }
}
