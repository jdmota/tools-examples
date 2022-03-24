// Experiment...

public class LinkedListIterator<T, c> {

  private Node<T> curr;

  // states available, end refine alive;

  // empty := head == null * tail == null;
  // notEmpty := unique(head) in withNext * head != null * tail != null;

  public LinkedListIterator(Node<T> head)
    // unique(head) => unique(this) 
  {
    curr = head;
  }

  public boolean hasNext()
    // pure(this) => (result == true * pure(this) in available) +
    //               (result == false * pure(this) in end)
  {
    return curr != null;
  }

  public T next()
    // full(this) in available => full(this) * pure(result)
  {
    T value = curr.getValue();
    curr = curr.getNext();
    return value;
  }

  protected void finalize()
    // unique(this) => unique(c)
  {

  }
}
