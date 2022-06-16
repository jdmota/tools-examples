public final class Node {
  public FileReader value;
  /*@ nullable @*/ public Node next;

  public Node(FileReader value, /*@ nullable @*/ Node next) {
    this.value = value;
    this.next = next;
  }
}
