public final class LinkedList {
  private /*@ spec_public @*/ int size;
  /*@ nullable @*/ private /*@ spec_public @*/ Node head;
  /*@ nullable @*/ private /*@ spec_public @*/ Node tail;
  //@ private spec_public ghost \seq nodeList;
  //@ private spec_public ghost \seq values;

  /*@ public model \locset footprint;
    @ accessible footprint: nodeList;
    @ accessible \inv: footprint;
    @ represents footprint = size, head, tail, nodeList, values,
    @    (\infinite_union \bigint i; 0 <= i < nodeList.length; ((Node)nodeList[i]).*);
    @*/

  /*@ invariant
    @   nodeList.length == size &&
    @   nodeList.length == values.length &&
    @   nodeList.length <= Integer.MAX_VALUE &&
    @   (\forall \bigint i; 0 <= i < nodeList.length;
    @       (\exists Node n; n == nodeList[i] && n.value != null)) &&
    @   (\forall \bigint i; 0 <= i < values.length;
    @       (\exists FileReader f; f == values[i] && f != null)) &&
    @   ((nodeList == \seq_empty && head == null && tail == null)
    @    || (nodeList != \seq_empty && head != null && tail != null &&
    @         tail.next == null && head == (Node)nodeList[0] &&
    @         tail == (Node)nodeList[nodeList.length-1])) &&
    @   (\forall \bigint i; 0 <= i < nodeList.length-1;
    @       ((Node)nodeList[i]).next == (Node)nodeList[i+1]) &&
    @   (\forall \bigint i; 0 <= i < nodeList.length;
    @     (\forall \bigint j; 0 <= j < nodeList.length;
    @       (Node)nodeList[i] == (Node)nodeList[j] ==> i == j
    @   )) &&
    @   (\forall \bigint i; 0 <= i < values.length;
    @      values[i] == ((Node)nodeList[i]).value);
    @*/

  /*@
    @ normal_behavior
    @ assignable \nothing;
    @ ensures values == \seq_empty;
    @ ensures \fresh(footprint);
    @*/
  public LinkedList() {
    head = null;
    tail = null;
    size = 0;
    //@ set nodeList = \seq_empty;
    //@ set values = \seq_empty;
  }

  /*@
    @ normal_behavior
    @ requires values.length + (\bigint)1 <= Integer.MAX_VALUE;
    @ assignable footprint;
    @ ensures values == \seq_concat(\old(values), \seq_singleton(value));
    @ ensures \new_elems_fresh(footprint);
    @*/
  public void add(FileReader value) {
    final Node n = new Node(value, null);
    if (head == null) {
      head = n;
    } else {
      tail.next = n;
    }
    tail = n;
    size++;
    //@ set nodeList = \seq_concat(nodeList, \seq_singleton(tail));
    //@ set values = \seq_concat(values, \seq_singleton(value));
  }

  /*@
    @ normal_behavior
    @ requires values.length > 0;
    @ assignable footprint;
    @ ensures
    @   values == \seq_sub(\old(values), 1, \old(values).length) &&
    @   \result == (FileReader)\old(values)[0];
    @ ensures \subset(footprint, \old(footprint));
    @*/
  public FileReader remove() {
    FileReader result = head.value;
    if (head.next != null) {
      head = head.next;
    } else {
      head = null;
      tail = null;
    }
    size--;
    //@ set nodeList = \seq_sub(nodeList, 1, \seq_length(nodeList));
    //@ set values = \seq_sub(values, 1, \seq_length(values));
    return result;
  }

  /*@
    @ normal_behavior
    @ assignable \nothing;
    @ ensures \invariant_for(\result);
    @ ensures \fresh(\result) && \fresh(\result.footprint);
    @ ensures \result.seen == \seq_empty && \result.to_see == values;
    @ ensures \result.list == this;
    @*/
  public LinkedListIterator iterator() {
    return new LinkedListIterator(this, head);
  }
}
