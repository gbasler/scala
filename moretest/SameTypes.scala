object Test {

  sealed abstract class Animal

  sealed abstract class Habitat

  case object Wild extends Habitat

  case object Domestic extends Habitat

  sealed abstract class Eatable

  case object IsEatable extends Eatable

  case object NotEatable extends Eatable

  final case class Pig(habitat: Habitat, eatable: Eatable)

}