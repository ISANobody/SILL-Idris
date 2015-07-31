module RegularTrees
import Data.Vect
import Data.HVect
import Data.Fin
import Data.Vect.Quantifiers as Q

-- Regular trees are potentially infinite trees that have a finite number of
-- equivalences classes of subtrees. A convenient way of specifying these trees
-- in text is via a fixed point operator. E.g., mu x. Foo(Foo(x)) specifies
-- a "tree" that is an infinite stream of Foo constructors.

-- This development focuses on working with these fixed point representations
-- of trees. As future work, it would be reasonable to allow equational
-- specifications of trees and allow for them to be treated as codata.

-- The main result of this work will be to develop a descision proceedure for
-- equality on these trees. It looks like this won't be propositional equality,
-- so we will need to define our own custom proof of equality. This seems
-- problematic, perhaps the two notions coincide when we look at the trees as
-- codata?

-- This fixpoint approach will, up to Future Work, allow us to specify trees
-- that are regular by construction. To do that we need some finite set of
-- connectives and their associated arities. In practice, we will want to work
-- potentially infnite sets of connectives and allow the fact that a finite
-- sized term can only use a finite number of these connectives to help us. To
-- be fully formal we should define a notion of a sublanguage and then define
-- equality at the join of their two languages (in the lattice of maps by
-- domains). Instead we will allow for infinite sets of connectives and trust
-- users to be safe (ugh). This will presumebably increase our usage of
-- assert_total and believe_me a bit more than would be ideal.

-- A language specification is just a funciton from the type of connectives to
-- their arities. This does not allow for variable arity connectives (i.e.,
-- overloaded connectives) or infinite airty connectives.

LanguageSpec : Type -> Type
LanguageSpec t = t -> Nat

-- A term in our tree language is then a Mu or a variable or a connective with
-- the appropriate number of subterms. A better version this would allow for
-- Mu's to actually be binders (De Bruijn encoded)
-- A better encoding would also enforce well-formedness
-- Specifically:
--   Mu Var should be banned
--   Mu Mu is pretty pointless
--   Open terms probably should be banned

-- TODO These names are horrible
data Clopen = Closed | Open
data IsVar = YesVar | NotVar
data IsMu = YesMu | NotMu

-- TODO Better Names
total
clopenMangle : Vect n Clopen -> Clopen
clopenMangle [] = Closed
clopenMangle (Open::_) = Open
clopenMangle (Closed::cs) = clopenMangle cs

data RegularTree : (t -> Nat) -> Clopen -> IsVar -> IsMu -> Type where
  Mu : RegularTree l Open NotVar NotMu -> RegularTree l Closed NotVar YesMu
  Var : RegularTree l Open YesVar NotMu
  Con : (c:t) 
     -> {l:t -> Nat} 
     -> {clopens : Vect (l c) Clopen} 
     -> {isvars : Vect (l c) IsVar} 
     -> {ismus : Vect (l c) IsMu} 
     -> HVect (zipWith3 (RegularTree l) clopens isvars ismus)
     -> RegularTree l (clopenMangle clopens) NotVar YesMu

-- Some injectivity lemmas
injective_Mu : (p:Mu s = Mu t) -> (s = t)
injective_Mu Refl = Refl

injective_Connect1 : (Con c cs = Con d ds) -> (c = d)
injective_Connect1 Refl = Refl
injective_Connect2 : (Con c cs = Con d ds) -> (cs = ds)
injective_Connect2 Refl = Refl

injective_HVect_Cons1 : {ts1:HVect v1} -> {ts2:HVect v2}
                     -> (t1::ts1 = t2::ts2) -> (t1 = t2)
injective_HVect_Cons1 Refl = Refl
injective_HVect_Cons2 : {ts1:HVect v1} -> {ts2:HVect v2}
                     -> (t1::ts1 = t2::ts2) -> (ts1 = ts2)
injective_HVect_Cons2 Refl = Refl

instance DecEq (HVect []) where
  decEq [] [] = Yes Refl

instance (DecEq t,DecEq (HVect ts)) => DecEq (HVect (t::ts)) where
  decEq (t1::ts1) (t2::ts2) with (decEq t1 t2)
    decEq (t::ts1) (t::ts2) | Yes Refl with (decEq ts1 ts2)
      decEq (t::ts) (t::ts) | Yes Refl | Yes Refl = Yes Refl
      decEq (t::ts1) (t::ts2) | Yes Refl 
                              | No ctr = No (ctr . injective_HVect_Cons2)
    decEq (t1::ts1) (t2::ts2) | No ctr = No (ctr . injective_HVect_Cons1)

instance DecEq t => DecEq (RegularTree {t} l c v m) where
  decEq (Con c cs)
        (Con d ds) = ?p


{- Can't call decEq on HVect w/o decEq on RegularTree, which would remove the
- point of this ....
flexDec : DecEq t => {l:t -> Nat}
         -> (s1:RegularTree l c1 v1 m1)
         -> (s2:RegularTree l c2 v2 m2)
         -> Dec (s1 = s2)
flexDec (Con c cs) (Con d ds) with (decEq c d)
  flexDec (Con c cs) (Con d ds) | (No contra) = No (contra . injective_Connect1)
  flexDec (Con c cs) (Con c ds) | (Yes Refl) with (_)
    flexDec (Con c cs) (Con c ds) | (Yes Refl) | with_pat = ?flexDec_rhs
-}

{-
-- An instance for syntactic equality. Might need to tag this in the
-- future
instance (DecEq t) => DecEq (RegularTree {t} l) where
  decEq Var Var = Yes Refl
  decEq (Mu s) (Mu t) with (decEq s t)
    decEq (Mu s) (Mu s) | Yes Refl = Yes Refl
    decEq (Mu s) (Mu t) | No p = No (p . injective_Mu)
  decEq (Connect c cs) (Connect d ds) with (decEq c d)
    decEq (Connect c cs) (Connect c ds) | Yes Refl 
    with (assert_total (decEq cs ds))
      decEq (Connect c cs) (Connect c cs) | Yes Refl | Yes Refl = Yes Refl
      decEq (Connect c cs) (Connect c ds) | Yes Refl | No p 
        = No (p . injective_Connect2)
    decEq (Connect c cs) (Connect d ds) | No p = No (p . injective_Connect1)
  decEq Var (Mu _) = No (\p => case p of Refl impossible)
  decEq Var (Connect _ _) = No (\p => case p of Refl impossible)
  decEq (Mu _) Var = No (\p => case p of Refl impossible)
  decEq (Mu _) (Connect _ _) = No (\p => case p of Refl impossible)
  decEq (Connect _ _) Var = No (\p => case p of Refl impossible)
  decEq (Connect _ _) (Mu _) = No (\p => case p of Refl impossible)

-- Some simple examples
-- These are kind of ugly. Would we normally want some syntactic sugar?
-- TODO move these to a separate file

exampleSpec : LanguageSpec (Fin 3)
exampleSpec = finToNat

exampleType1 : RegularTree exampleSpec
exampleType1 = Connect 0 []

exampleType2 : RegularTree exampleSpec
exampleType2 = Mu (Connect 1 [Connect 1 [Var]])

exampleType3 : RegularTree exampleSpec
exampleType3 = Mu (Connect 1 [Connect 1 [Connect 1 [Var]]])

-- To unfold Mu fixed points we'll need substitution. If we were tracking the
-- openness of trees at the type level we could probably make this more
-- efficient.
-- WARNING, this has a, hopefully safe, usage of assert_total
subst : RegularTree l -> RegularTree l -> RegularTree l
subst x Var = x
subst _ (Mu y) = Mu y
subst x (Connect c v) = Connect c (assert_total (map (subst x) v))

-- To avoid later comparisons on Mu headed terms, we'll need to unfold them
-- In principle, this could be shown to return something that's appropriately
-- equivalent but w/o the Mu head.
-- Additionally, the case for Var is a little worrisome. We should only be
-- calling unfold on closed terms.
unfold : RegularTree l -> RegularTree l
unfold (Mu x) = subst (Mu x) x
unfold Var = Var
unfold (Connect c v) = Connect c v

-- The following encodes the standard circular coinductive reasoning for
-- equality on infinite trees. These should probably syntax driven but aren't.
-- That's "ok" since we will also use assert_total and believe_me more than we
-- should. To see the problem consider (Mu x = Mu y).
-- See http://www.cs.ru.nl/bachelorscripties/2013/Robin_Munsterman___4070968___Equality_of_infinite_objects.pdf
-- TODO better names
-- TODO Only work on closed terms
data RTEq_ : Vect n (RegularTree l,RegularTree l)
                  -> RegularTree l
                  -> RegularTree l 
                  -> Type where
  Assumpt : Elem (s,t) hyp -> RTEq_ hyp s t
  RTEqMuL : RTEq_ hyp (unfold (Mu s)) t -> RTEq_ hyp (Mu s) t
  RTEqMuR : RTEq_ hyp s (unfold (Mu t)) -> RTEq_ hyp s (Mu t)
  RTEqCon : All (uncurry (RTEq_ ((Connect c ss,Connect c ts)::hyp))) (zip ss ts)
         -> RTEq_ {l=l} hyp (Connect c ss) (Connect c ts)

-- Define a wrapper for starting out with no hypotheses
RTEq : RegularTree l -> RegularTree l -> Type
RTEq s t = RTEq_ [] s t

RTEq_case : (DecEq t) => {t:Type} -> {l:t->Nat} -> {x:RegularTree l} -> {y:RegularTree l}
         -> (Elem (x,y) hyp -> b)
         -> (RTEq_ hyp (unfold x) y -> b)
         -> (RTEq_ hyp x (unfold y) -> b)
         -> (  {c:t} 
            -> {ss:Vect (l c) (RegularTree l)} 
            -> {ts:Vect (l c) (RegularTree l)}
            -> All (uncurry (RTEq_ ((Connect c ss,Connect c ts)::hyp))) (zip ss ts) -> b)
         -> (RTEq_ hyp x y -> b)
RTEq_case f _ _ _ (Assumpt p) = f p
RTEq_case _ f _ _ (RTEqMuL p) = f p
RTEq_case _ _ f _ (RTEqMuR p) = f p
RTEq_case _ _ _ f (RTEqCon p) = f p

exampleEq1 : (RTEq exampleType1 exampleType1)
exampleEq1 = RTEqCon Nil

isRTEq0 : (DecEq t) => {l:t->Nat} -> (hyp:Vect n (RegularTree l,RegularTree l)) -> (x:RegularTree l) -> (y:RegularTree l) -> Dec (RTEq_ hyp x y)
isRTEq1 : (DecEq t) => {l:t->Nat}
       -> (hyp:Vect n (RegularTree l,RegularTree l))
       -> {p:Not (Elem (x,y) hyp)}
       -> (x:RegularTree l) -> (y:RegularTree l) -> Dec (RTEq_ hyp x y)
isRTEq0_ : (DecEq t) => {l:t->Nat} -> (hyp:Vect n (RegularTree l,RegularTree l))
       -> (z:(RegularTree l,RegularTree l)) -> Dec (uncurry (RTEq_ hyp) z)

isRTEq0 hyp x y with (isElem (x,y) hyp)
  isRTEq0 hyp x y | (Yes prf) = Yes (Assumpt prf)
  isRTEq0 hyp x y | (No contra) = assert_total (isRTEq1 {p=contra} hyp x y)

isRTEq0_ hyp (x,y) = isRTEq0 hyp x y


-- A better version wouldn't need this Var case
isRTEq1 hyp (Mu x) y with (isRTEq0 hyp (unfold (Mu x)) y)
  isRTEq1 hyp (Mu x) y | (Yes prf) = Yes (RTEqMuL prf)
  isRTEq1 hyp (Mu x) y | (No contra) = No believe_me
isRTEq1 hyp x (Mu y) with (isRTEq0 hyp x (unfold (Mu y)))
  isRTEq1 hyp x (Mu y) | (Yes prf) = Yes (RTEqMuR prf)
  isRTEq1 hyp x (Mu y) | (No contra) = No believe_me
isRTEq1 hyp (Connect c cs) (Connect d ds) with (decEq c d)
  isRTEq1 hyp (Connect c cs) (Connect c ds) | (Yes Refl) 
  with (Q.all{P=(uncurry (RTEq_ ((Connect c cs,Connect c ds)::hyp)))}
              (isRTEq0_ ((Connect c cs, Connect c ds) :: hyp))
              (zip cs ds))
    isRTEq1 hyp (Connect c cs) (Connect c ds) | (Yes Refl) | (Yes prf) 
    = Yes (RTEqCon prf)
    isRTEq1 hyp (Connect c cs) (Connect c ds) | (Yes Refl) | (No contra) 
    = No believe_me
  isRTEq1 hyp (Connect c cs) (Connect d ds) | (No contra) = No believe_me
isRTEq1 _ _ _ = No believe_me

isRTEq : (DecEq t) => {l:t->Nat} 
      -> (x:RegularTree l) -> (y:RegularTree l) -> Dec (RTEq_ [] x y)
isRTEq = isRTEq0 []

-- TODO figure out if there is a better
getYes : (res : Dec p) -> case res of {Yes _ => p; No _ => ()}
getYes (Yes p) = p
getYes (No _) = ()

DecProofType : {a:Type} -> Dec a -> Type
DecProofType {a} (Yes _)  = a
DecProofType {a} (No _)   = a -> Void

decProof : {a:Type} -> (dec : Dec a) -> DecProofType dec
decProof (Yes x)  = x
decProof (No x)   = x
-}
