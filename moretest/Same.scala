object Test {

  sealed abstract class A

  case object A1 extends A

  case object A2 extends A

  sealed abstract class B

  case object B1 extends B

  case object B2 extends B

  sealed abstract class C

  final case class One(a: A, b: B) extends C

  final case class Two(b: B, a: A) extends C

  def foo(c: C): Unit = c match {
    case One(A1, B1) =>
        case One(A2, B1) =>
        case One(A1, B2) =>
        case One(A2, B2) =>
    case Two(B1, A1) =>
        case Two(B2, A1) =>
    //    case Two(B1, A2) =>
    //    case Two(B2, A2) =>
  }

  def `fool me`(c: C, a: A, b: B): Unit = (c, a, b) match {
    case (_: One, A1, B1) =>
    //    case One(A2, B1) =>
    //    case One(A1, B2) =>
    //    case One(A2, B2) =>
    case (_: Two, A1, B1) =>
    //    case Two(B2, A1) =>
    //    case Two(B1, A2) =>
    //    case Two(B2, A2) =>
  }
}

object Same {

  sealed abstract class A

  case object A1 extends A

  case object A2 extends A

  sealed abstract class B

  case object B1 extends B

  case object B2 extends B

  sealed abstract class C

  final case class One(a: A, b: B) extends C

  final case class Two(b: B, a: A) extends C

  // if we say that b implies two then we get a problem with this one:
  final case class Three(b: B) extends C

  // we could say: b and a implies two
  // but then following the same logic we will have
  // b implies three which will contradict if we are looking for two...
  // does the other direction make sense?
  // two implies b & a, three implies b ?
  // i think so...
  // so the formula would be:
  // two implies (A1 | A2) && (B1 | B2) ->
  // !TWO | ( (A1 | A2) && (B1 | B2) ) ->
  // (!TWO | A1 | A2) && (!TWO | B1 | B2)

  def foo(c: C): Unit = c match {
    case One(A1, B1) =>
    //    case One(A2, B1) =>
    //    case One(A1, B2) =>
    //    case One(A2, B2) =>
    case Two(B1, A1) =>
    //    case Two(B2, A1) =>
    //    case Two(B1, A2) =>
    //    case Two(B2, A2) =>
  }

  //  def foo2(c: C): Unit = c match {
  //    case _: Three =>
  //  }
}

//object Same {
//
//  sealed abstract class A
//
//  case object A1 extends A
//
//  case object A2 extends A
//
//  sealed abstract class B
//
//  case object B1 extends B
//
//  case object B2 extends B
//
//  sealed abstract class C
//
//  final case class One(a: A, b: B) extends C
//
//  final case class Two(a: A, b: B) extends C
//
//  def foo(c: C): Unit = c match {
//    case One(A1, B1) =>
////    case One(A2, B1) =>
////    case One(A1, B2) =>
////    case One(A2, B2) =>
//    case Two(A1, B1) =>
//    case Two(A1, B2) =>
//    case Two(A2, B1) =>
//  }
//}