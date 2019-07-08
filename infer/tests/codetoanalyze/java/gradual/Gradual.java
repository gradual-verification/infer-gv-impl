package codetoanalyze.java.gradual;

import javax.annotation.Nonnull;

class Foo {
  Object f;

  static Foo mystery() {
    return new Foo();
  }

  static Object takeNull(Foo x) {
    return x == null ? null : x.f;
  }

  static Object firstF(@Nonnull Foo x, Foo y, @Nonnull Foo z) {
    if (x.f != null) {
      return x.f;
    }
    if (y != null && y.f != null) {
      return y.f;
    }
    return z.f;
  }

  Object getF() {
    return f;
  }

  Object firstF(Foo y, @Nonnull Foo z) {
    return firstF(this, y, z);
  }

  static void complain(
    @Nonnull Foo a,
    @Nonnull Foo b,
    @Nonnull Foo c
  ) { }
}

class Bar {
  @Nonnull String s = "Hello, world!";

  String getSNullable() {
    return s;
  }

  @Nonnull String getS() {
    return s;
  }
}

class MatchInstrTests {
  static void assignChecksLhs() {
    Foo x = null;
    x.f = null; // should warn about null deference
  }

  static void assignChecksRhs() {
    Foo x = null;
    Object y = x.f; // should warn about null dereference
  }

  static void assignMakesNonnull() {
    Foo x = Foo.mystery();
    Object y1 = x.f; // should warn about possible null dereference
    x = new Foo();
    Object y2 = x.f; // shouldn't warn
  }

  static void assignChecksLhsFieldAnnot() {
    Bar x = new Bar();
    x.s = null; // should warn about field annotation violation
  }

  static void assignAllowsNonnullFieldAnnot() {
    Bar x = new Bar();
    x.s = "henlo worl"; // shouldn't warn
  }

  static void assignAllowsNullableFieldAnnot() {
    Foo x = new Foo();
    x.f = null; // shouldn't warn
  }

  static void assumeChecksCond() {
    Foo x = new Foo();
    if (x.f == null) { // should warn about null dereference
      x = null;
    }
  }

  static void assumeMakesNonnull() {
    Foo x = Foo.mystery();
    if (x != null) {
      Object y = x.f; // shouldn't warn
    }
  }

  static void callStaticAcceptsNullFirstArg() {
    Foo x = null;
    Object y = Foo.takeNull(x); // shouldn't warn
  }

  static void callStaticChecksAllAnnots() {
    Foo x = Foo.mystery();
    Foo y = Foo.mystery();
    Foo z = Foo.mystery();
    Object o = Foo.firstF(x, y, z); // should warn about x and z
  }

  static void callMethodRejectsNullReceiver() {
    Foo x = null;
    Object y = x.getF(); // should warn about null dereference
  }

  static void callMethodChecksAllAnnots() {
    Foo x = new Foo();
    Foo y = Foo.mystery();
    Foo z = Foo.mystery();
    Object o = x.firstF(y, z); // should warn about z
  }

  static void callMakesNonnull() {
    Bar x = new Bar();
    String s = x.getSNullable();
    int l1 = s.length(); // should warn about possible null dereference
    s = x.getS();
    int l2 = s.length(); // shouldn't warn
  }

  static void fieldGivesNullableAnnot() {
    Foo x = new Foo();
    Object y = x.f;
    int z = y.hashCode(); // should warn about null dereference
  }

  static void fieldGivesNonnullAnnot() {
    Bar x = new Bar();
    String s = x.s;
    int l = s.length(); // shouldn't warn
  }

  static void arrayItemsNullable() {
    String[] ss = new String[2];
    ss[0] = "Hello, world!";
    String a = ss[0];
    String b = ss[1];
    int al = a.length(); // should warn about possible null dereference
    int bl = b.length(); // should warn about null dereference
  }

  static void castsAreStillNull() {
    Foo x = (Foo) null;
    Object y = x.f; // should warn about null dereference
  }

  static void logicChecksCompoundExprs() {
    Foo x = new Foo();
    Foo a = Foo.mystery();
    Foo b = Foo.mystery();
    Foo c = Foo.mystery();
    // looks like true case should say b is nonnull
    // but the compound cond expr is split b/c of short-circuiting
    if (!((a == null || b == null) && !(b == x && c != null))) {
      Foo.complain(a, b, c); // should warn about a, b, c
    } else {
      Foo.complain(a, b, c); // should warn about a, b, c
    }
  }
}
