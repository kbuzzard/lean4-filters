class Foo (α : Type) where
  b : Bool

class Bar (α : Type) extends Foo α where
  n : Nat

instance baz : Foo Int := {b := true }

instance : Bar Int := {n := 37, toFoo := baz }
