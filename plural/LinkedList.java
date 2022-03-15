class Node<T> {
  private T value;
  private Node<T> next;
  
  // states withNext, withoutNext refine alive;

  // withNext := pure(value) && unique(next)
  // withoutNext := pure(value) && none(next)

  public Node(T value)
    // pure(value) -o unique(this) in withoutNext
  {
    this.value = value;
    this.next = null;
  }

  public Node<T> getNext()
    // unique(this) in withNext -o unique(this) in withoutNext && unique(result)
  {
    return this.next;
  }

  public void setNext(Node<T> next)
    // unique(this) in withoutNext && unique(next) -o unique(this) in withNext
  {
    this.next = next;
  }

  public T getValue() 
    // pure(this) -o pure(this) && pure(result)
  {
    return this.value;
  }
}

public class LinkedList<T> {

  private Node<T> head;
  private Node<T> tail;

  // states empty, notEmpty refine alive;
  
  // empty := head == null && tail == null;
  // notEmpty := unique(head) in withNext && head != null && tail != null;
  
  public LinkedList()
    // 1 -o unique(this) in empty
  {
    head = null;
    tail = null;
  }

  public void add(T element)
    // full(this) && pure(element) -o full(this) in notEmpty
  {
    Node<T> n = new Node<>(element);
    if (head == null) {
      head = n;
      tail = n;
    } else {
      tail.setNext(n);
      tail = n;
    }
  }

  public T remove()
    // full(this) in notEmpty -o full(this) && pure(result)
  {
    T result = head.getValue();
    head = head.getNext();
    if (head == null) {
      tail = null;
    }
    return result;
  }
}
