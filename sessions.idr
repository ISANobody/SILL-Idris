module Sessions
import Data.Vect
import Data.Fin

-- This should have a more informative type
data A :  Type where
  Mu : A  -> A
  Var : A 
  Nullary : A 
  Unary : A -> A 
  Binary : A -> A -> A
  Many : List A -> A

injective_Mu : (p:Mu a = Mu b) -> (a = b)
injective_Mu Refl = Refl

injective_Unary : (p:Unary a = Unary b) -> (a = b)
injective_Unary Refl = Refl

injective_BinaryL : (p:Binary a b = Binary c d) -> (a = c)
injective_BinaryL Refl = Refl

injective_BinaryR : (p:Binary a b = Binary c d) -> (b = d)
injective_BinaryR Refl = Refl

injective_Many : (p:Many f = Many g) -> (f = g)
injective_Many Refl = Refl

-- I wonder if this is hinding somewhere
cong2: {t1:Type} -> {t2:Type} -> {a:t1} -> {b:t1} -> {c:t2} -> {d:t2}
       -> {f:t1->t2 -> _}
       -> (a=b) -> (c=d) -> (f a c = f b d)
cong2 Refl Refl = Refl

cong3: {t1:Type} -> {t2:Type} -> {t3:Type} 
       -> {a:t1} -> {b:t1} -> {c:t2} -> {d:t2} -> {x:t3} -> {y:t3}
       -> {f:t1->t2->t3-> _}
       -> (a=b) -> (c=d) -> (x=y) -> (f a c x = f b d y)
cong3 Refl Refl Refl = Refl

-- This is disgustingly long. The totality checker is terrible
instance DecEq A where
  decEq Var Var = Yes Refl
  decEq Nullary Nullary = Yes Refl
  decEq (Unary a) (Unary b) with (decEq a b)
    | Yes prf = Yes (cong prf)
    | No prf = No (prf . injective_Unary)
  decEq (Mu a) (Mu b) with (decEq a b)
    | Yes prf = Yes (cong prf)
    | No prf = No (prf . injective_Mu)
  decEq (Binary a b) (Binary c d) with (decEq a c,decEq b d)
    | (Yes p1,Yes p2) = Yes (cong2{f=Binary} p1 p2)
    | (No p,_) = No (p . injective_BinaryL)
    | (_,No p) = No (p . injective_BinaryR)
  decEq (Many v1) (Many v2) with (assert_total (decEq v1 v2))
    | Yes p = Yes (cong p)
    | No p = No (p . injective_Many)
  decEq Var Nullary = No (\x => case x of Refl impossible)
  decEq Var (Mu _) = No (\x => case x of Refl impossible)
  decEq Var (Unary _) = No (\x => case x of Refl impossible)
  decEq Var (Binary _ _) = No (\x => case x of Refl impossible)
  decEq Var (Many _) = No (\x => case x of Refl impossible)
  decEq Nullary Var = No (\x => case x of Refl impossible)
  decEq Nullary (Mu _) = No (\x => case x of Refl impossible)
  decEq Nullary (Unary _) = No (\x => case x of Refl impossible)
  decEq Nullary (Binary _ _) = No (\x => case x of Refl impossible)
  decEq Nullary (Many _) = No (\x => case x of Refl impossible)
  decEq (Mu _) Nullary = No (\x => case x of Refl impossible)
  decEq (Mu _) Var = No (\x => case x of Refl impossible)
  decEq (Mu _) (Unary _) = No (\x => case x of Refl impossible)
  decEq (Mu _) (Binary _ _) = No (\x => case x of Refl impossible)
  decEq (Mu _) (Many _) = No (\x => case x of Refl impossible)
  decEq (Unary _) Nullary = No (\x => case x of Refl impossible)
  decEq (Unary _) (Mu _) = No (\x => case x of Refl impossible)
  decEq (Unary _) Var = No (\x => case x of Refl impossible)
  decEq (Unary _) (Binary _ _) = No (\x => case x of Refl impossible)
  decEq (Unary _) (Many _) = No (\x => case x of Refl impossible)
  decEq (Binary _ _) Nullary = No (\x => case x of Refl impossible)
  decEq (Binary _ _) (Mu _) = No (\x => case x of Refl impossible)
  decEq (Binary _ _) (Unary _) = No (\x => case x of Refl impossible)
  decEq (Binary _ _) Var = No (\x => case x of Refl impossible)
  decEq (Binary _ _) (Many _) = No (\x => case x of Refl impossible)
  decEq (Many _) Nullary = No (\x => case x of Refl impossible)
  decEq (Many _) (Mu _) = No (\x => case x of Refl impossible)
  decEq (Many _) (Unary _) = No (\x => case x of Refl impossible)
  decEq (Many _) Var = No (\x => case x of Refl impossible)
  decEq (Many _) (Binary _ _) = No (\x => case x of Refl impossible)

-- Would more precise kinding allow us to drop the assert total?
total subst : A -> A -> A
subst x Var = x
subst x (Mu y) = Mu y
subst _ Nullary = Nullary
subst x (Unary a) = Unary (subst x a)
subst x (Binary a b) = Binary (subst x a) (subst x b)
subst x (Many v) = Many (assert_total (map (subst x) v))

total unfold : A -> A
unfold (Mu x) = subst (Mu x) x
unfold Var = Var
unfold Nullary = Nullary
unfold (Unary a) = Unary a
unfold (Binary a b) = Binary a b
unfold (Many v) = Many v

data AEq' : Vect n (A,A) -> A -> A -> Type where
  Assmp : Elem (a,a') hyp -> AEq' hyp a a'
  AEqNull : AEq' _ Nullary Nullary
  AEqUnary : AEq' ((Unary a,Unary a')::hyp) a a' -> AEq' hyp (Unary a) 
                                                             (Unary a')
  AEqBinary : AEq' ((Binary a1 b1,Binary a2 b2)::hyp) a1 a2
           -> AEq' ((Binary a1 b1,Binary a2 b2)::hyp) b1 b2
           -> AEq' hyp (Binary a1 b1) (Binary a2 b2)
  AEqMuL : AEq' hyp (unfold (Mu a)) a' -> AEq' hyp (Mu a) a'
  AEqMuR : AEq' hyp a (unfold (Mu a')) -> AEq' hyp a (Mu a')
  
AEq : A -> A -> Type
AEq a a' = AEq' Nil a a'

-- isAEq0 for searching through hypothesis
-- isAEq1 for doing matching
total isAEq0 : (hyp:Vect n (A,A)) -> (x:A) -> (y:A) -> Dec (AEq' hyp x y)
total isAEq1 : (hyp:Vect n (A,A)) -> {p:Not (Elem (x,y) hyp)} 
            -> (x:A) -> (y:A) -> Dec (AEq' hyp x y)

isAEq0 hyp x y with (isElem (x,y) hyp)
  | Yes i = Yes (Assmp i)
  | No p = assert_total (isAEq1 {p} hyp x y)

isAEq1 _ Nullary Nullary = Yes AEqNull
isAEq1 hyp (Unary a) (Unary b) with (isAEq0 ((Unary a,Unary b)::hyp) a b)
  | Yes p = Yes (AEqUnary p)
  | No p = No believe_me
isAEq1 hyp (Binary a1 b1) (Binary a2 b2) 
  with (isAEq0 ((Binary a1 b1,Binary a2 b2)::hyp) a1 a2
       ,isAEq0 ((Binary a1 b1,Binary a2 b2)::hyp) b1 b2)
  | (Yes p1,Yes p2) = Yes (AEqBinary p1 p2)
  | _ = No believe_me
isAEq1 hyp (Mu x) y with (isAEq0 hyp (unfold (Mu x)) y)
  | Yes p = Yes (AEqMuL p)
  | _ = No believe_me
isAEq1 hyp x (Mu y) with (isAEq0 hyp x (unfold (Mu y)))
  | Yes p = Yes (AEqMuR p)
  | _ = No believe_me
isAEq1 _ _ _ = No believe_me

total isAEq : (x:A) -> (y:A) -> Dec (AEq x y)
isAEq x y = assert_total (isAEq0 [] x y)

a1 : AEq Nullary Nullary
a1 = proof search

a1' : AEq (Unary Nullary) (Unary Nullary)
a1' = proof search

a3 : AEq (Mu (Unary Nullary)) (Unary Nullary)
a3 = getProof
  where getProof : {prf: AEq (Mu (Unary Nullary)) (Unary Nullary)}
                 -> {auto yep : isAEq (Mu (Unary Nullary)) (Unary Nullary) = Yes prf}
                 -> AEq (Mu (Unary Nullary)) (Unary Nullary)
        getProof {prf} = prf

a4 : AEq (Mu (Unary (Unary Var))) (Mu (Unary Var))
a4 = getProof
  where getProof : {prf: AEq (Mu (Unary (Unary Var))) (Mu (Unary Var))}
                 -> {auto yep : isAEq (Mu (Unary (Unary Var))) (Mu (Unary Var)) = Yes prf}
                 -> AEq (Mu (Unary (Unary Var))) (Mu (Unary Var))
        getProof {prf} = prf

m2 : A
m2 = (Mu (Unary (Unary Var)))

m3 : A
m3 = (Mu (Unary (Unary (Unary Var))))

a5 : AEq m2 m3
a5 = getProof
  where getProof : {prf: AEq m2 m3} -> {auto yep : isAEq m2 m3 = Yes prf}
                 -> AEq m2 m3
        getProof {prf} = prf

{-
data A : Bool -> Bool -> Bool -> Type where
  Mu : A False False _ -> A True False False
  Var : A False True True
  Nullary : A False False False
  Unary : A m v o -> A False False o
  Binary : A m1 v1 o1 -> A m2 v2 o2 -> A False False (o1 || o2)


-- I guess this is sort of contextual?
total bigEq : (x:A m1 v1 o1) -> (y:A m2 v2 o2)
            -> Dec (x = y)
bigEq Nullary Nullary = Yes Refl
bigEq Var Var = Yes Refl
bigEq {o1} {o2} (Unary {m=m} {v=v} a) 
                (Unary {m=m'} {v=v'} b) with (decEq m m',decEq v v',decEq o1 o2
                                             ,bigEq a b)
  | (Yes p1,Yes p2,Yes p3,Yes receq) = Yes ?p -}

{-
total subst' : A m1 v1 c1 -> A m2 v2 c2 -> (c3 ** ((A (m2 || (v2 && m1))
                                                     (v2 && v1)
                                                     c3)
                                                 ,(c3 = c2 && c1)))
subst' _ Nullary = (_ ** (Nullary,Refl))
subst' w (Unary a) with (subst' w a)
  | (c3** (a',aeq)) = (c3 ** (Unary a',aeq))
subst' w (Binary a b) with (subst' w a, subst' w b)
  | ((ca**(a',aeq)),(cb**(b',beq))) = ((ca||cb)**(Binary a' b',?substBinary))
subst' w Var = (_ ** (w,Refl))
subst' w (Mu a) = (_ ** (Mu a,Refl))

total subst : A m1 v1 c1 -> A m2 v2 c2 -> A (m2 || (v2 && m1)) 
                                             (v2 && v1) (c2 && c1)
subst a1 a2 with (subst' a1 a2)
 | (_**(a',aeq)) = replace aeq a' 

total unfold' : A m False o -> (o=False) -> (m'** (A False False m',m' = False))
unfold' (Mu a) _  = (_**(subst (Mu a) a,?unfoldMu))
unfold' Nullary _ = (_**(Nullary,Refl))
unfold' (Unary a) p = (_**(Unary a,p))
unfold' (Binary a b) p = (_**(Binary a b,p))

total unfold : A m False False -> A False False False
unfold a with (unfold' a Refl)
 | (_**(a',aeq)) = replace aeq a'

-- We prove equality by circular coinduction
-- We carry along a vector of assumptions and use them
-- The goal would be to prove [] |- a = a'
data AEq' : Vect n (A False False False,A False False False) -- Assumptions
        -> A _ _ False -> A _ _ False -> Type where
  Assmp : Elem (a,a') hyp -> AEq' hyp a a'
  AEqNull : AEq' _ Nullary Nullary
  AEqUnary : AEq' ((Unary a,Unary a')::hyp) a a' -> AEq' hyp (Unary a) 
                                                             (Unary a')
  AEqMuL : AEq' hyp (unfold (Mu a)) a' -> AEq' hyp (Mu a) a'
  AEqMuR : AEq' hyp a (unfold (Mu a')) -> AEq' hyp a (Mu a')

AEq : A _ _ False -> A _ _ False -> Type
AEq a a' = AEq' Nil a a'

-- One prime peforms lookup, two primes is the core
total isAEq' : (a:A _ _ False) -> (a':A _ _ False) -> Dec (AEq' hyp a a')
total isAEq'' : (a:A _ _ False) -> (a':A _ _ False) -> Dec (AEq' hyp a a')

isAEq'' Nullary Nullary = Yes AEqNull
isAEq''{hyp} (Unary a) (Unary a') with (isAEq'{hyp=((Unary a,Unary a')::hyp)} a a')
  | Yes p = Yes (AEqUnary p)
  | No _ = No (believe_me)

total isAEq : (a:A _ _ False) -> (a':A _ _ False) -> Dec (AEq a a')
isAEq = isAEq'{hyp=[]}

{- 
a1 : AEq Nullary Nullary
a1 = proof search

a1' : AEq (Unary Nullary) (Unary Nullary)
a1' = proof search

a3 : AEq (Mu (Unary Nullary)) (Unary Nullary)
a3 = proof search

a4 : AEq (Mu (Unary (Unary Var))) (Mu (Unary Var))
a4 = proof search

m2 : A True False False
m2 = (Mu (Unary (Unary Var)))

m3 : A True False False
m3 = (Mu (Unary (Unary (Unary Var))))

a5 : AEq m2 m3
a5 = getProof
  where getProof : {prf: AEq m2 m3} -> {auto yep : isAEq m2 m3 = Yes prf}
                 -> AEq m2 m3
        getProof {prf} = prf
-}
-}

-- Seems like this has to be in the Data.Vect somewhere, right?
data InVect : (i : Fin n) -> Vect n v -> v -> Type where
  Found : {V:Vect n v} -> InVect FZ (t :: V) t
  Later : {V:Vect n v} -> InVect k V t 
          -> InVect (FS k) (u :: V) t

data Label = InL | InR


-- The type of a session type is just the maximum variable index
-- I'm not sure if doing this via a newtype would be clearer
-- Also, this representation doesn't guarantee contractiviness
data SessionType : Type where
  Closed : SessionType
  One    : SessionType
  SendD  : Type -> SessionType -> SessionType
  RecvD  : Type -> SessionType -> SessionType
  Intern : (Label -> SessionType) -> SessionType
  Extern : (Label -> SessionType) -> SessionType

allClosed : Vect n SessionType
allClosed{n=Z} = Nil
allClosed{n=S k} = Closed :: allClosed

update : Fin n -> t -> Vect n t -> Vect n t
update i e v = updateAt i (const e) v

using (G, G':Vect n SessionType)
  data Process : Vect n SessionType -> SessionType -> Type where
    Close  : Process allClosed One
    Wait   : InVect i G One -> Process (update i Closed G) s 
             -> Process G s
    SendDL : InVect i G (RecvD t s') -> t -> Process (update i s' G) s
             -> Process G s
    SendDR : t -> Process G s -> Process G (SendD t s)
    RecvDL : InVect i G (SendD t s') -> (t -> Process (update i s' G) s)
             -> Process G s
    InternR: (l:Label) -> {choices:Label -> SessionType} 
             -> Process G (choices l)
             ->  Process G (Intern choices)
    ExternR: {choices:(Label -> SessionType)}
             -> ((l:Label) -> Process G (choices l))
             -> Process G (Extern choices)
    Bind   : Process [] s' -> Process (s'::G) s -> Process G s
    Forward: InVect i (update i s allClosed) s 
             -> Process (update i s allClosed) s

t1 : Process [One] One
t1 = Wait Found Close

t2 : Process [RecvD Int (RecvD Float One)] One
t2 = SendDL Found 6 (SendDL Found 8.3 (Wait Found Close))

t3 : Process [] (SendD Bool (SendD String One))
t3 = SendDR True (SendDR "asdf" Close)

t4 : Process [] (Intern (const One))
t4 = InternR InL Close

-- This seems like it's needed to get help the type checker
-- It reads like the problem is that in t5 it's unclear what
-- the set of labels Extern makes it's choices over (since const One
-- allows any type for its second argument). However, the label type,
-- Labels, is hardcoded....
t5_branches : Label -> Process [] One
t5_branches _ = Close

t5 : Process [] (Extern (const One))
t5 = ExternR t5_branches

t6 : Process [] One
t6 = Bind Close 
          (Bind t3 
                (Wait (Later Found) 
                      (RecvDL Found (\_ =>
                              RecvDL Found (\_ =>
                                      Wait Found Close)))))

t7 : Process [] (SendD String One)
t7 = Bind t3 (RecvDL Found (\_ => (Forward Found)))

t8 : Process [SendD (Process [] (SendD Int One)) One] One
t8 = RecvDL Found (\p =>
     (Bind p
     (RecvDL Found (\_ =>
     (Wait Found
     (Forward (Later Found)))))))
