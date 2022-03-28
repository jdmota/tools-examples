public final class Node {  
  // Give me the segment between "this" inclusive and "end" exclusive

  /*@
  resource state() = Perm(next, 1) ** Perm(value, 1);
  
  resource seg(Node end) =
    this == end ? true : Perm(next, 1) ** Perm(value, 1) ** next != null ** next.seg(end);

  requires this.seg(end);
  pure seq<FileReader> segment(Node end) =
    this == end ?
      seq<FileReader> {} :
      \unfolding this.seg(end) \in (
        seq<FileReader> { value } + next.segment(end)
      );
  @*/

  FileReader value;
  Node next;
}
