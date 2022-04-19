import edu.cmu.cs.plural.annot.*;

@Similar("p")
@Refine({
  @States(value={"withValue", "withoutValue"}, dim="dimValue"),
  @States(value={"withNext", "withoutNext"}, dim="dimNext")
})
@ClassStates({
  @State(name="withValue", inv="p(value)"),
  @State(name="withoutValue", inv="true"),
  @State(name="withNext", inv="unique(next) in withValue,dimNext * next != null"),
  @State(name="withoutNext", inv="next == null")
})
public class Node<T> {
  @Apply("p")
  private Node<T> next;
  private T value;

  @Perm(ensures="unique(this!fr) in withValue,withoutNext")
  public Node(@PolyVar(value="p", returned=false) T val) {
    value = val;
    next = null;
  }

  @Unique(requires="withNext", ensures="withoutNext", use=Use.FIELDS)
  @ResultUnique(ensures="withValue,dimNext")
  @ResultApply("p2")
  public Node<T> getNext() {
    Node<T> n = next;
    next = null;
    return n;
  }

  @Unique(requires="withoutNext", ensures="withNext", use=Use.FIELDS)
  public void setNext(
    @Unique(requires="withValue,dimNext", returned=false) @Apply("p") Node<T> n
  ) {
    next = n;
  }

  @Unique(requires="withValue", ensures="withoutValue", use=Use.FIELDS)
  @ResultPolyVar("p")
  public T getValue() {
    return value;
  }

  @Unique(guarantee="dimNext", use=Use.FIELDS)
  @TrueIndicates("withNext")
  @FalseIndicates("withoutNext")
  public boolean hasNext() {
    if (next == null) {
      return false;
    }
    return true;
  }
}
