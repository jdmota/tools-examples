public class Main {
  /*@
    @ normal_behavior
    @ requires true;
    @ ensures true;
    @*/
  public static void main(String[] args) {
    LinkedList list = new LinkedList();
    FileReader f1 = new FileReader();
    FileReader f2 = new FileReader();
    FileReader f3 = new FileReader();
    list.add(f1);
    list.add(f2);
    list.add(f3);
    useFiles(list);
  }

  /*@
    @ normal_behavior
    @ requires
    @   \invariant_for(list) &&
    @   (\forall \bigint i; 0 <= i < list.values.length;
    @       (\exists FileReader f; f == list.values[i] && f != null && \invariant_for(f) && f.state == FileReader.STATE_INIT)) &&
    @   (\forall \bigint i; 0 <= i < list.values.length;
    @     (\forall \bigint j; 0 <= j < list.values.length;
    @       (FileReader)list.values[i] == (FileReader)list.values[j] ==> i == j
    @   ));
    @ assignable (\infinite_union \bigint i; 0 <= i < list.values.length; ((FileReader)list.values[i]).footprint);
    @ ensures
    @   (\forall \bigint i; 0 <= i < list.values.length;
    @     (\exists FileReader f; f == list.values[i] && f != null && \invariant_for(f) && f.state == FileReader.STATE_CLOSED));
    @*/
  public static void useFiles(LinkedList list) {
    LinkedListIterator it = list.iterator();
    recursive(list, it);
  }

  /*@
    @ normal_behavior
    @ requires
    @   \invariant_for(it) &&
    @   \invariant_for(list) &&
    @   it.list == list &&
    @   (\forall \bigint i; 0 <= i < it.seen.length;
    @     (\exists FileReader f; f == it.seen[i] && f != null && f.state == FileReader.STATE_CLOSED && \invariant_for(f))) &&
    @   (\forall \bigint i; 0 <= i < it.to_see.length;
    @     (\exists FileReader f; f == it.to_see[i] && f != null && f.state == FileReader.STATE_INIT && \invariant_for(f))) &&
    @   (\forall \bigint i; 0 <= i < it.seen.length;
    @     (\forall \bigint j; 0 <= j < it.seen.length;
    @       (FileReader)it.seen[i] == (FileReader)it.seen[j] ==> i == j
    @   )) &&
    @   (\forall \bigint i; 0 <= i < it.to_see.length;
    @     (\forall \bigint j; 0 <= j < it.to_see.length;
    @       (FileReader)it.to_see[i] == (FileReader)it.to_see[j] ==> i == j
    @   ));
    @ assignable it.footprint;
    @ assignable (\infinite_union \bigint i; 0 <= i < it.to_see.length; ((FileReader)it.to_see[i]).footprint);
    @ measured_by it.to_see.length;
    @ ensures
    @   \invariant_for(it) &&
    @   \invariant_for(list) &&
    @   it.list == list &&
    @   (\forall \bigint i; 0 <= i < it.seen.length;
    @     (\exists FileReader f; f == it.seen[i] && f != null && f.state == FileReader.STATE_CLOSED && \invariant_for(f))) &&
    @   (\forall \bigint i; 0 <= i < it.seen.length;
    @     (\forall \bigint j; 0 <= j < it.seen.length;
    @       (FileReader)it.seen[i] == (FileReader)it.seen[j] ==> i == j
    @   )) &&
    @   it.to_see == \seq_empty;
    @*/
  private static void recursive(LinkedList list, LinkedListIterator it) {
    if (it.hasNext()) {
      FileReader f = it.next();
      use(f);
      recursive(list, it);
    }
  }

  /*@
    @ normal_behavior
    @ requires \invariant_for(f);
    @ requires f.state == FileReader.STATE_INIT;
    @ assignable f.footprint;
    @ ensures \invariant_for(f);
    @ ensures f.state == FileReader.STATE_CLOSED;
    @*/
  private static void use(FileReader f) {
    f.open();
    /*@
      @ loop_invariant \invariant_for(f) && f.state == FileReader.STATE_OPENED;
      @ assignable f.footprint;
      @ decreases f.remaining;
      @*/
    while (!f.eof()) {
      f.read();
    }
    f.close();
  }

  /*@
    @ normal_behavior
    @ requires
    @   \invariant_for(list) &&
    @   (\forall \bigint i; 0 <= i < list.values.length;
    @       (\exists FileReader f; f == list.values[i] && f != null && \invariant_for(f) && f.state == FileReader.STATE_INIT)) &&
    @   (\forall \bigint i; 0 <= i < list.values.length;
    @     (\forall \bigint j; 0 <= j < list.values.length;
    @       (FileReader)list.values[i] == (FileReader)list.values[j] ==> i == j
    @   ));
    @ assignable (\infinite_union \bigint i; 0 <= i < list.values.length; ((FileReader)list.values[i]).footprint);
    @ ensures
    @   (\forall \bigint i; 0 <= i < list.values.length;
    @     (\exists FileReader f; f == list.values[i] && f != null && \invariant_for(f) && f.state == FileReader.STATE_CLOSED));
    @*/
  public static void useFiles2(LinkedList list) {
    LinkedListIterator it = list.iterator();
    /*@
      @ loop_invariant
      @   \invariant_for(it) &&
      @   \invariant_for(list) &&
      @   it.list == list &&
      @   (\forall \bigint i; 0 <= i < it.seen.length;
      @     (\exists FileReader f; f == it.seen[i] && f != null && f.state == FileReader.STATE_CLOSED && \invariant_for(f))) &&
      @   (\forall \bigint i; 0 <= i < it.to_see.length;
      @     (\exists FileReader f; f == it.to_see[i] && f != null && f.state == FileReader.STATE_INIT && \invariant_for(f))) &&
      @   (\forall \bigint i; 0 <= i < it.seen.length;
      @     (\forall \bigint j; 0 <= j < it.seen.length;
      @       (FileReader)it.seen[i] == (FileReader)it.seen[j] ==> i == j
      @   )) &&
      @   (\forall \bigint i; 0 <= i < it.to_see.length;
      @     (\forall \bigint j; 0 <= j < it.to_see.length;
      @       (FileReader)it.to_see[i] == (FileReader)it.to_see[j] ==> i == j
      @   ));
      @ assignable it.footprint;
      @ assignable (\infinite_union \bigint i; 0 <= i < it.to_see.length; ((FileReader)it.to_see[i]).footprint);
      @ decreases it.to_see.length;
      @*/
    while (it.hasNext()) {
      FileReader f = it.next();
      use(f);
    }
  }
}
