package codetoanalyze.java.gradual;

class Foo {
  Foo f;
}

class Dereference {
  void f() {
    Foo x = null;
    Foo y = x.f.f;

    int[][] a = null;
    int b = a[0][0];

    Foo m = new Foo();
    m.f = null;
  }
}
