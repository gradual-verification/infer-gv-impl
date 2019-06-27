class Foo {
  Object f;
}

class Dereference {
  void f() {
    Foo x = null;
    Object y = x.f;
  }
}
