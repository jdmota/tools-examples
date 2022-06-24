/*@
lemma void distinct_nodes(Node n1, Node n2)
  requires node(n1, ?n1n, ?n1v) &*& node(n2, ?n2n, ?n2v);
  ensures node(n1, n1n, n1v) &*& node(n2, n2n, n2v) &*& n1 != n2;
{
  open node(n1, _, _);
  open node(n2, _, _);
  close node(n1, _, _);
  close node(n2, _, _);
}

lemma void add_lemma(Node n1, Node n2, Node n3)
  requires lseg(n1, n2, ?l) &*& node(n2, n3, ?value) &*& node(n3, ?n4, ?v);
  ensures lseg(n1, n3, append(l, cons(value, nil))) &*& node(n3, n4, v);
{
  distinct_nodes(n2, n3);
  open lseg(n1, n2, l);
  if (n1 != n2) {
    assert node(n1, ?next, _) &*& lseg(next, n2, _);
    distinct_nodes(n1, n3);
    add_lemma(next, n2, n3);
    assert node(n1, next, _) &*& lseg(next, n3, _);
  }
  close lseg(n1, n3, _);
}

lemma void append_cons_not_nil<t>(list<t> l, t value, list<t> l2)
  requires true;
  ensures append(l, cons(value, l2)) != nil;
{
  switch (l) {
    case nil: assert true;
    case cons(x, xs): assert true;
  }
}

lemma void too_much_fraction(real a, real b, Node n)
  requires [a]n.next |-> _ &*& [b]n.next |-> _ &*& a + b > 1;
  ensures false;
{}

lemma void iterator_advance(Node h, Node n, Node t)
  requires [1/2]lseg(h, n, ?a) &*& [1/2]node(n, ?next, ?val1) &*& [1/2]nodes(next, ?b) &*& [1/2]lseg(h, t, ?list) &*& [1/2]node(t, null, ?val2);
  ensures [1/2]lseg(h, next, append(a, cons(val1, nil))) &*& [1/2]nodes(next, b) &*& [1/2]lseg(h, t, list) &*& [1/2]node(t, null, val2);
{
  open lseg(h, n, a);
  if (h == n) {
    open lseg(h, t, list);
    if (h == t) {
      open [1/2]node(t, _, _);
      open [1/2]node(t, _, _);
      close node(t, null, val2);
    } else {
      open [1/2]lseg(_, t, _);
      open [1/2]nodes(next, b);
      open [1/2]node(t, _, _);
      open [1/2]node(t, _, _);
      open [1/2]node(next, _, _);
      open [1/2]node(next, _, _);
      distinct_nodes(h, next);
      close [1/2]lseg(h, next, cons(val1, nil));
    }
  } else {
    if (h == t) {
      open [1/2]lseg(h, t, _);
      close node(h, _, _);
      close node(h, null, _);
      open [1/2]lseg(?next0, n, _);
      assert next0 == null;
      open [1/2]node(next0, _, _);
      assert false;
    } else if (h == next) {
      open [1/2]nodes(next, b);
      if (h == null) {
        open [1/2]node(h, _, _);
        assert false;
      } else {
        open [1/2]lseg(h, t, list);
        open node(h, _, _);
        too_much_fraction(1/2, 1, h);
        assert false;
      }
    } else {
      open [1/2]node(h, ?hNext, _);
      open [1/2]node(h, _, _);
      iterator_advance(hNext, n, t);
      close node(h, _, _);
      close [1/2]lseg(h, t, list);
      close [1/2]lseg(h, next, append(a, cons(val1, nil)));
    }
  }
}

lemma void prepare_iterator_3(Node h, Node t)
  requires [?f]lseg(h, t, ?list) &*& [f]node(t, null, ?value);
  ensures [f]nodes(h, append(list, cons(value, nil)));
{
  open lseg(_, _, _);
  open node(h, ?next, _);
  assert h != null;
  open node(t, _, _);
  assert t != null;
  if (h == t) {
    close [f]nodes(t, cons(value, nil));
  } else {
    prepare_iterator_3(next, t);
  }
}

lemma void prepare_iterator_2(LinkedList javalist)
  requires [1/2]llist(javalist, ?h, ?t, ?list);
  ensures [1/2]javalist.head |-> h &*& [1/2]javalist.tail |-> t &*& [1/2]nodes(h, list);
{
  open llist(_, _, _, _);
  if (h == null) {

  } else {
    prepare_iterator_3(h, t);
  }
}

lemma void prepare_iterator(LinkedList javalist)
  requires llist(javalist, ?h, ?t, ?list);
  ensures iterator_base(javalist, h, list, nil, list);
{
  open llist(_, _, _, _);
  if (h == null) {

  } else {
    prepare_iterator_2(javalist);
  }
}

lemma void dispose_iterator_2(Node h, Node t)
  requires [1/2]lseg(h, t, ?l) &*& [1/2]node(t, null, ?value) &*& [1/2]lseg(h, null, ?list) &*& list == append(l, cons(value, nil));
  ensures lseg(h, t, l) &*& node(t, null, value) &*& list == append(l, cons(value, nil));
{
  if (h == null) {
    open lseg(_, _, _);
    append_cons_not_nil(l, value, nil);
    assert false;
  } else {
    open lseg(h, null, list);
    open lseg(h, t, l);
    if (l == nil) {
      close node(t, null, _);
    } else {
      open node(h, ?next, _);
      dispose_iterator_2(next, t);
    }
  }
}

lemma void dispose_iterator(LinkedListIterator it)
  requires iterator(?javalist, it, null, ?list, list, nil);
  ensures llist(javalist, _, _, list);
{
  open iterator(_, _, _, _, _, _);
  open iterator_base(_, _, _, _, _);
  open llist(_, ?h, ?t, _);
  if (list == nil) {
  
  } else {
    dispose_iterator_2(h, t);
  }
}

lemma void empty_seq(Node n)
  requires lseg(n, n, ?l);
  ensures lseg(n, n, l) &*& l == nil;
{
  open lseg(n, n, l);
  close lseg(n, n, l);
}

lemma void lseg_concat(Node n1, Node n2, Node n3)
  requires lseg(n1, n2, ?a) &*& lseg(n2, n3, ?b) &*& node(n3, ?n4, ?v);
  ensures lseg(n1, n3, append(a, b)) &*& node(n3, n4, v);
{
  open lseg(n1, n2, a);
  if (n1 == n2) {

  } else {
    open node(n1, ?next, _);
    distinct_nodes(n1, n3);
    lseg_concat(next, n2, n3);
    close lseg(n1, n3, append(a, b));
  }
}

lemma void append_inversion<t>(list<t> seg, t value)
  requires true;
  ensures take(length(append(seg, cons(value, nil))) - 1, append(seg, cons(value, nil))) == seg &*&
          drop(length(append(seg, cons(value, nil))) - 1, append(seg, cons(value, nil))) == cons(value, nil) &*&
          nth(length(append(seg, cons(value, nil))) - 1, append(seg, cons(value, nil))) == value;
{
  switch (seg) {
    case nil: assert true;
    case cons(x, xs): {
      append_inversion(xs, value);
      length_append(xs, cons(value, nil));
    }
  }
}

lemma void append_take_drop_2_aux<t>(list<t> xs)
  requires true;
  ensures append(take(length(xs), xs), drop(length(xs), xs)) == xs;
{
  switch (xs) {
    case nil: assert true;
    case cons(x, tail): append_take_drop_2_aux(tail);
  }
}

lemma void append_take_drop_2<t>(int n, list<t> xs)
  requires 0 <= n && n <= length(xs);
  ensures append(take(n, xs), drop(n, xs)) == xs;
{
  if (n == length(xs)) {
    append_take_drop_2_aux(xs);
  } else {
    append_take_drop(n, xs);
  }
}
@*/