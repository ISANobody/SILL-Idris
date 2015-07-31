module Test

import Data.Vect.Quantifiers

foo : (xs:Vect n Type) -> Dec (All (\z => Int = z) xs)
foo Nil = Yes Nil
foo (x::xs) with (decEq x Int)
  foo (Int::xs) | Refl = ?p
