object Test {

  sealed abstract class C

  trait A extends C

  trait B extends C

  trait AB extends A with B

  def `A missing`(c: C) = c match {
    case _: B => ???
  }

  def exhaustive(c: C) = c match {
    case _: AB => ???
  }
}
