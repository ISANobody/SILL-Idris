module Sessions

import RegularTrees
import Data.Vect.Quantifiers as Q

-- Unfortunately, we need to decide equality on Type in order to handle T/\S
-- and T => S. Type is not (cannot?) be an instance of DeqEq, so we'll create a
-- custom Serializeable class that will have a string to name each instance and
-- also serialization and deserialization methods. There is almost certainly a
-- better solution to doing this (maybe some reflection).

data PrimTy = I

instance DecEq PrimTy where
  decEq I I = Yes Refl

-- This makes me wonder if this would work better in Haskell with
-- -XEverythingOn. I think we could just add arbitary type equality constraints
-- there and let the solver deal with it.
total primTyInterp : PrimTy -> Type
primTyInterp I = Int

data Labels = A | B | D | C

data SType : Type where
  SendD : PrimTy -> SType
  RecvD : PrimTy -> SType
  One   : SType
  SendC : SType
  RecvC : SType

injective_SendD : (SendD s = SendD t) -> (s = t)
injective_SendD Refl = Refl

injective_RecvD : (RecvD s = RecvD t) -> (s = t)
injective_RecvD Refl = Refl

instance DecEq SType where
  decEq One One = Yes Refl
  decEq SendC SendC = Yes Refl
  decEq RecvC RecvC = Yes Refl
  decEq (SendD s) (SendD t) with (decEq s t)
    decEq (SendD s) (SendD s) | Yes Refl = Yes Refl
    decEq (SendD s) (SendD t) | No p = No (p . injective_SendD)
  decEq (RecvD s) (RecvD t) with (decEq s t)
    decEq (RecvD s) (RecvD s) | Yes Refl = Yes Refl
    decEq (RecvD s) (RecvD t) | No p = No (p . injective_RecvD)
  decEq One SendC = No (\p => case p of Refl impossible)
  decEq One RecvC = No (\p => case p of Refl impossible)
  decEq One (SendD _) = No (\p => case p of Refl impossible)
  decEq One (RecvD _) = No (\p => case p of Refl impossible)
  decEq SendC One = No (\p => case p of Refl impossible)
  decEq SendC RecvC = No (\p => case p of Refl impossible)
  decEq SendC (SendD _) = No (\p => case p of Refl impossible)
  decEq SendC (RecvD _) = No (\p => case p of Refl impossible)
  decEq RecvC One = No (\p => case p of Refl impossible)
  decEq RecvC SendC = No (\p => case p of Refl impossible)
  decEq RecvC (SendD _) = No (\p => case p of Refl impossible)
  decEq RecvC (RecvD _) = No (\p => case p of Refl impossible)
  decEq (SendD _) One = No (\p => case p of Refl impossible)
  decEq (SendD _) SendC = No (\p => case p of Refl impossible)
  decEq (SendD _) RecvC = No (\p => case p of Refl impossible)
  decEq (SendD _) (RecvD _) = No (\p => case p of Refl impossible)
  decEq (RecvD _) One = No (\p => case p of Refl impossible)
  decEq (RecvD _) SendC = No (\p => case p of Refl impossible)
  decEq (RecvD _) RecvC = No (\p => case p of Refl impossible)
  decEq (RecvD _) (SendD _) = No (\p => case p of Refl impossible)

STypeArities : LanguageSpec SType
STypeArities (SendD _) = 1
STypeArities (RecvD _) = 1
STypeArities RecvC = 2
STypeArities SendC = 2
STypeArities One = 0

SessionType : Type
SessionType = RegularTree STypeArities

sendD : PrimTy -> SessionType -> SessionType
sendD i s = Connect (SendD i) [s]
recvD : PrimTy -> SessionType -> SessionType
recvD i s = Connect (RecvD i) [s]
sendC : SessionType -> SessionType -> SessionType
sendC s1 s2 = Connect SendC [s1,s2]
recvC : SessionType -> SessionType -> SessionType
recvC s1 s2 = Connect RecvC [s1,s2]
one : SessionType
one = Connect One []
