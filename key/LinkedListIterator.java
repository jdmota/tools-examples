public final class LinkedListIterator {
  private /*@ spec_public @*/ LinkedList list;
  /*@ nullable @*/ private Node curr;
  //@ private ghost \bigint index;
  //@ private spec_public ghost \seq seen;
  //@ private spec_public ghost \seq to_see;

  /*@ public model \locset footprint;
    @ accessible footprint: \nothing;
    @ accessible \inv: footprint, list.footprint;
    @ represents footprint = list, curr, index, seen, to_see;
    @*/

  /*@ invariant
    @   0 <= index && index <= list.values.length &&
    @   (\forall \bigint i; 0 <= i < seen.length;
    @      (\exists FileReader f; f == seen[i] && f != null)) &&
    @   (\forall \bigint i; 0 <= i < to_see.length;
    @      (\exists FileReader f; f == to_see[i] && f != null)) &&
    @   seen == \seq_sub(list.values, 0, index) &&
    @   to_see == \seq_sub(list.values, index, list.values.length) &&
    @   (index < list.values.length ? curr == (Node)list.nodeList[index] : curr == null) &&
    @   \invariant_for(list);
    @*/

  /*@
    @ normal_behavior
    @ requires
    @   l.head == head &&
    @   \invariant_for(l);
    @ assignable \nothing;
    @ ensures
    @   list == l &&
    @   seen == \seq_empty &&
    @   to_see == l.values &&
    @   \invariant_for(l);
    @ ensures \fresh(footprint);
    @*/
  public LinkedListIterator(LinkedList l, /*@ nullable @*/ Node head) {
    this.list = l;
    this.curr = head;
    //@ set index = 0;
    //@ set seen = \seq_empty;
    //@ set to_see = l.values;
  }

  /*@
    @ normal_behavior
    @ assignable \strictly_nothing;
    @ ensures \result == (to_see.length > 0);
    @*/ 
  public boolean hasNext() {
    return curr != null;
  }

  /*@
    @ normal_behavior
    @ requires to_see.length > 0;
    @ accessible list.footprint;
    @ accessible footprint;
    @ assignable footprint;
    @ ensures
    @   seen == \seq_concat(\old(seen), \seq_singleton(\result)) &&
    @   to_see == \seq_sub(\old(to_see), 1, \old(to_see).length) &&
    @   \result == (FileReader)\old(to_see)[0];
    @ ensures list == \old(list);
    @*/
  public FileReader next() {
    FileReader value = curr.value;
    curr = curr.next;
    //@ set index = index + 1;
    //@ set seen = \seq_concat(seen, \seq_singleton(value));
    //@ set to_see = \seq_sub(to_see, 1, \seq_length(to_see));
    return value;
  }
}
