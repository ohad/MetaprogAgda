module Exe1 where

open import Basics public

-- \section{Zipping Lists of Compatible Shape}

data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X

infixr 4 _,_

zip0 : {S T : Set} -> List S -> List T -> List (S * T)
zip0 <>        <>        = <>
zip0 (s , ss)  (t , ts)  = (s , t) , zip0 ss ts
zip0 _         _         = <>  -- a dummy value, for cases we should not reach

data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

length : {X : Set} -> List X -> Nat
length <>        = zero
length (x , xs)  = suc (length xs)

data Vec (X : Set) : Nat -> Set where
  <>   :                               Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)

zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> <> = <>
zip1 (s , ss) (t , ts) = (s , t) , zip1 ss ts

vec : forall {n X} -> X -> Vec X n
vec {zero} x = <>
vec {suc n} x = x , vec x

vapp :  forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp <> <> = <>
vapp (f , fs) (s , ss) = (f s) , vapp fs ss

vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap f ss = vapp (vec f) ss

zip2 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip2 ss ts = vapp (vapp (vec _,_) ss) ts


--[Finite sets and projection from vectors]

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

forgetFin : {n : Nat} -> Fin n -> Nat
forgetFin zero = 0
forgetFin (suc n) = suc (forgetFin n)

proj : forall {n X} -> Vec X n -> Fin n -> X
proj (x , xs) zero = x
proj (x , xs) (suc i) = proj xs i

-- Some useful helper functions
nudge : {n : Nat} -> Fin n -> Fin (suc n)
nudge zero = suc zero
nudge (suc i) = suc (nudge i)

upto : (n : Nat) -> Vec (Fin n) n
upto zero = <>
upto (suc n₁) = zero , vmap nudge (upto n₁)

tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {n} f = vmap f (upto n) 

-- Functors and Applicatives

record EndoFunctor (F : Set -> Set) : Set1 where
  field
    map  : forall {S T} -> (S -> T) -> F S -> F T
open EndoFunctor {{...}} public

record Applicative (F : Set -> Set) : Set1 where
  infixl 2 _<*>_
  field
    pure    : forall {X} -> X -> F X
    _<*>_   : forall {S T} -> F (S -> T) -> F S -> F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _<*>_ o pure }
open Applicative {{...}} public

applicativeVec  : forall {n} -> Applicative \ X -> Vec X n
applicativeVec  = record { pure = vec; _<*>_ = vapp }
endoFunctorVec  : forall {n} -> EndoFunctor \ X -> Vec X n
endoFunctorVec  = applicativeEndoFunctor

applicativeFun : forall {S} -> Applicative \ X -> S -> X
applicativeFun = record
  {  pure    = \ x s -> x              -- also known as K (drop environment)
  ;  _<*>_   = \ f a s -> f s (a s)    -- also known as S (share environment)
  }

record Monad (F : Set -> Set) : Set1 where
  field
    return  : forall {X} -> X -> F X
    _>>=_   : forall {S T} -> F S -> (S -> F T) -> F T
  monadApplicative : Applicative F
  monadApplicative = record
    {  pure   = return
    ;  _<*>_  = \ ff fs -> ff >>= \ f -> fs >>= \ s -> return (f s) }
open Monad {{...}} public

drop : {n : Nat} -> {X : Set} -> Vec X (suc n) -> Vec X n
drop (x , xs) = xs

mult : {n : Nat} -> {X : Set} -> Vec (Vec X n) n -> Vec X n
mult {zero} vss = <>
mult {suc n} ((x , v) , vs) = x , mult (map drop  vs)

monadVec : {n : Nat} -> Monad \ X -> Vec X n
monadVec = record { return  = vec; _>>=_ = λ vs f → mult (map f vs)}

applicativeId : Applicative id
applicativeId = record { pure = id; 
                         _<*>_ = id }

applicativeComp : forall {F G} -> Applicative F -> Applicative G -> Applicative (F o G)
applicativeComp {F} {G} aF aG = 
  record {   
           pure  = pure {{aF}} o pure ;  
           _<*>_  = _<*>_ {{aF}} o 
                         map {{applicativeEndoFunctor {{aF}}}} _<*>_ 
  }

record Monoid (X : Set) : Set where
  infixr 4 _&_
  field
    neut  : X
    _&_   : X -> X -> X
  monoidApplicative : Applicative \ _ -> X
  monoidApplicative = 
    record { 
      pure = λ _ → neut; 
      _<*>_ = λ x y → x & y 
    }
open Monoid {{...}} public -- it's not obvious that we'll avoid ambiguity

--Show by construction that the pointwise product of |Applicative|s is
-- |Applicative|.

ptwsApplicative : forall { F G } -> Applicative F -> Applicative G 
                    -> Applicative (\ X -> (F X) * (G X))
ptwsApplicative aF aG = 
  record { 
    pure = λ x → (pure x) , (pure x);
    _<*>_ = vv (λ fF gG → vv (λ sF sG → (fF <*> sF) , (gG <*> sG)))
  }

record Traversable (F : Set -> Set) : Set1 where
  field
    traverse :  forall {G S T}{{AG : Applicative G}} ->
                (S -> G T) -> F S -> G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record { map = traverse }
open Traversable {{...}} public

traversableVec : {n : Nat} -> Traversable \ X -> Vec X n
traversableVec = record { traverse = vtr } where
  vtr :  forall {n G S T}{{_ : Applicative G}} ->
         (S -> G T) -> Vec S n -> G (Vec T n)
  vtr {{aG}} f <>        = pure {{aG}} <>
  vtr {{aG}} f (s , ss)  = pure {{aG}} _,_ <*> f s <*> vtr f ss

transpose : forall {m n X} -> Vec (Vec X n) m -> Vec (Vec X m) n
transpose = traverse id

crush :  forall {F X Y}{{TF : Traversable F}}{{M : Monoid Y}} ->
         (X -> Y) -> F X -> Y
crush {{M = M}} =
  traverse {T = One}{{AG = monoidApplicative {{M}}}}  -- |T| arbitrary


{-Show that |Traversable| is closed under identity and composition.
What other structure does it preserve?-}

idTraverse : Traversable id
idTraverse = record { traverse = id }

compTraverse : forall {F G} -> Traversable F -> Traversable G 
                 -> Traversable (F o G)
compTraverse tF tG = 
  record { 
    traverse = λ h s → traverse {{tF}} (traverse {{tG}} h) s
  }

-- Todo: Finish on a by-need basis?

--\section{Arithmetic}
_+Nat_ : Nat -> Nat -> Nat
zero +Nat y  = y
suc x +Nat y = suc (x +Nat y)

_*Nat_ : Nat -> Nat -> Nat
zero *Nat y = zero
suc x *Nat y = y +Nat (x *Nat y)

--\section{Normal Functors}

record Normal : Set1 where
  constructor _/_
  field
    Shape  : Set
    size   : Shape -> Nat
  <!_!>N : Set -> Set
  <!_!>N X = Sg Shape \ s -> Vec X (size s)
open Normal public
infixr 0 _/_

VecN : Nat -> Normal
VecN n = One / pure n

ListN : Normal
ListN = Nat / id


K : Set -> Normal
K A = A / (λ a → zero)

I : Normal
I = One / (λ _ → 1)

_+N_ : Normal -> Normal -> Normal
(ShF / szF) +N (ShG / szG) = (ShF + ShG) / vv szF <?> szG

_*N_ : Normal -> Normal -> Normal
(ShF / szF) *N (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f +Nat szG g

nInj : forall {X}(F G : Normal) -> <! F !>N X + <! G !>N X -> <! F +N G !>N X
nInj F G (tt , ShF , xs) = (tt , ShF) , xs
nInj F G (ff , ShG , xs) = (ff , ShG) , xs

data _^-1_ {S T : Set}(f : S -> T) : T -> Set where
  from : (s : S) -> f ^-1 f s

nCase : forall {X} F G (s : <! F +N G !>N X) -> nInj F G ^-1 s
nCase F G ((tt , ShF) , xs) = from (tt , ShF , xs)
nCase F G ((ff , ShG) , xs) = from (ff , ShG , xs)

nOut : forall {X}(F G : Normal) -> <! F +N G !>N X -> <! F !>N X + <! G !>N X
nOut F G xs' with nCase F G xs'
nOut F G .(nInj F G xs) | from xs = xs

_++_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +Nat n)
<> ++ ys = ys
(x , xs) ++ ys = x , (xs ++ ys)

nPair : forall {X}(F G : Normal) -> <! F !>N X * <! G !>N X -> <! F *N G !>N X
nPair F G ((sF , vF) , (sG , vG)) = (sF , sG) , (vF ++ vG )

concatSurjectivity : forall {m n : Nat} {X} -> (x : Vec X (m +Nat n)) -> (vv \ (u : Vec X m) (v : Vec X n) -> u ++ v)  ^-1 x
concatSurjectivity {zero} v = from (<> , v)
concatSurjectivity {suc m} (x , v) with concatSurjectivity {m} v
concatSurjectivity {suc m} (x , .(u ++ w)) | from (u , w) = from ((x , u) , w)

nProj : forall { X } F G (s : <! F *N G !>N X) -> (nPair F G) ^-1 s
nProj F G ((sF , sG) , vFG) with concatSurjectivity {size F sF} vFG 
nProj F G ((sF , sG) , .(u ++ w)) | from (u , w) = from ((sF , u) , (sG , w)) 

monmult : forall {X} -> <! ListN !>N X -> <! ListN !>N X -> <! ListN !>N X
monmult (n , xs) (m , ys) = (n +Nat m) , (xs ++ ys)

listNMonoid : {X : Set} -> Monoid (<! ListN !>N X)
listNMonoid = λ {X} → record { neut = zero , <>; _&_ = monmult }

sumMonoid : Monoid Nat
sumMonoid = record { neut = 0; _&_ = _+Nat_ }

normalTraversable : (F : Normal) -> Traversable <! F !>N
normalTraversable F = record
  { traverse = \ {{aG}} f -> vv \ s xs -> pure {{aG}}  (_,_ s) <*> traverse f xs }

_oN_ : Normal -> Normal -> Normal
F oN (ShG / szG) = <! F !>N ShG / crush {{normalTraversable F}} szG

sizeT : forall {F}{{TF : Traversable F}}{X} -> F X -> Nat
sizeT = crush (\ _ -> 1)

normalT : forall F {{TF : Traversable F}} -> Normal
normalT F = F One / sizeT

--shapeT : forall {F}{{TF : Traversable F}}{X} -> F X -> F One
--shapeT = traverse (\ _ -> <>)

one : forall {X} -> X -> <! ListN !>N X
one x = 1 , (x , <>)

contentsT : forall {F}{{TF : Traversable F}}{X} -> F X -> <! ListN !>N X
contentsT = crush one

--[normal morphisms]

_-N>_ : Normal -> Normal -> Set
F -N> G = (s : Shape F) -> <! G !>N (Fin (size F s))

nMorph : forall {F G} -> F -N> G -> forall {X} -> <! F !>N X -> <! G !>N X
nMorph f (s , xs)  with f s
...                | s' , is = s' , map (proj xs) is

--Show how to compute the normal morphism representing a given natural
--transformation.

morphN : forall {F G} -> (forall {X} -> <! F !>N X -> <! G !>N X) -> F -N> G
morphN {F} f s = f (s , upto (size F s))

--[Hancock's tensor]
_><_ : Normal -> Normal -> Normal
(ShF / szF) >< (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f *Nat szG g

swap : (F G : Normal) -> (F >< G) -N> (G >< F)
swap F G x = {!!}

--drop : (F G : Normal) -> (F >< G) -N> (F oN G)
--drop F G x = {!!}


--\section{Proving Equations}



record MonoidOK X {{M : Monoid X}} : Set where
  field
    absorbL  : (x : X) ->      neut & x == x
    absorbR  : (x : X) ->      x & neut == x
    assoc    : (x y z : X) ->  (x & y) & z == x & (y & z)


natMonoidOK : MonoidOK Nat
natMonoidOK = record
  {  absorbL  = \ _ -> refl
  ;  absorbR  = _+zero
  ;  assoc    = assoc+
  }  where    -- see below
  _+zero : forall x -> x +Nat zero == x
  zero   +zero                  = refl
  suc n  +zero rewrite n +zero  = refl

  assoc+ : forall x y z -> (x +Nat y) +Nat z  == x +Nat (y +Nat z)
  assoc+ zero     y z                       = refl
  assoc+ (suc x)  y z rewrite assoc+ x y z  = refl


_++L_ : forall {X } -> List X -> List X -> List X
<> ++L ys = ys
(x , xs) ++L ys = x , (xs ++L ys)

listMonoid : {X : Set} -> Monoid (List X)
listMonoid {X} = record { neut = <>; _&_ = _++L_ }

listMonoidOK : {X : Set} -> MonoidOK (List X)
listMonoidOK {X} = record 
  { 
    absorbL = λ _ → refl; 
    absorbR = _++L<>; 
    assoc = {!assoc++L!} 
  } where
    _++L<> : forall xs -> xs ++L <> == xs
    <> ++L<> = refl
    (x , xs) ++L<> rewrite xs ++L<> = refl

    lemma : forall xs ys y -> xs ++L (y , ys) == (xs ++L (y , <>)) ++L ys
    lemma <> ys y = refl
    lemma (x , xs) ys y rewrite lemma xs ys y = refl

    assoc++L : forall xs ys zs -> (xs ++L ys) ++L zs == xs ++L (ys ++L zs)
    assoc++L xs <> zs rewrite xs ++L<> = refl
    assoc++L xs (y , ys) zs rewrite lemma xs ys y 
                            |       assoc++L (xs ++L (y , <>)) ys zs 
                            |       lemma xs (ys ++L zs) y = refl

<>N : {X : Set} -> <! ListN !>N X
<>N = λ {X} → zero , <>

_++N_ : {X : Set} -> <! ListN !>N X -> <! ListN !>N X -> <! ListN !>N X
(zero , <>) ++N (n , ys) = n , ys
(suc m , (x , xs)) ++N (n , ys) with (m , xs) ++N (n , ys) 
(suc m , (x , xs)) ++N (n , ys) | k , r  = suc k , (x , r)

concatLength : forall {X : Set} m (xs : Vec X m) n (ys : Vec X n) -> ((m , xs) ++N (n , ys)) == ((m +Nat n) , (xs ++ ys))
concatLength zero <> n ys = refl
concatLength (suc m) (x , xs) n ys rewrite concatLength m xs n ys = refl

--_++<> : {X : Set} {n : Nat} -> (xs : Vec X n) -> rewrite
--MonoidOK.absorbR natMonoidOK n (xs ++ <> == xs) 
--xs ++<> = ?

listNMonoidOK : {X : Set} -> MonoidOK (<! ListN !>N X)
listNMonoidOK {X} = record 
  { 
    absorbL = λ x → refl; 
    absorbR = {!_++N<>!}; 
    assoc = {!!} 
  } where
    _++N<> : forall xs -> xs ++N <>N == xs
    (zero , <>) ++N<> = refl
    (suc m , (x , xs)) ++N<> rewrite concatLength m xs 0 <> 
--                             rewrite MonoidOK.absorbR 
                             with MonoidOK.absorbR natMonoidOK m
    (suc m , (x , xs)) ++N<> | q = {!!}

baz : {!!}
baz = MonoidOK.absorbR natMonoidOK 

{-
\begin{exe}[a not inconsiderable problem]
Find out what goes wrong when you try to state associativity of vector |++|,
let alone prove it. What does it tell you about our |==| setup?
\end{exe}
-}

record MonoidHom {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}(f : X -> Y) : Set where
  field
    respNeut  :                 f neut == neut
    resp&     : forall x x' ->  f (x & x') == f x & f x'

fstHom : forall {X} -> MonoidHom {<! ListN !>N X}{Nat} fst
fstHom = record { respNeut = refl; resp& = \ _ _ -> refl }

record EndoFunctorOK F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id == id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g == map (f o g)

{- fool'e errand -}
vecEndoFunctorOK : forall {n} -> EndoFunctorOK \ X -> Vec X n
vecEndoFunctorOK = record
  {  endoFunctorId  = {!!}
  ;  endoFunctorCo  = \ f g -> {!!}
  }

_=1=_ :  forall {l}{S : Set l}{T : S -> Set l}
         (f g : (x : S) -> T x) -> Set l
f =1= g = forall x -> f x == g x
infix 1 _=1=_

record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id =1= id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g =1= map (f o g)

--\section{Laws for |Applicative| and |Traversable|}

record ApplicativeOKP F {{AF : Applicative F}} : Set1 where
  field
    lawId :   forall {X}(x : F X) ->
      pure {{AF}} id <*> x == x
    lawCo :   forall {R S T}(f : F (S -> T))(g : F (R -> S))(r : F R) ->
      pure {{AF}} (\ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)
    lawHom :  forall {S T}(f : S -> T)(s : S) ->
      pure {{AF}} f <*> pure s == pure (f s)
    lawCom :  forall {S T}(f : F (S -> T))(s : S) ->
      f <*> pure s == pure {{AF}} (\ f -> f s) <*> f
  applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
  applicativeEndoFunctorOKP = record
    {  endoFunctorId = lawId
    ;  endoFunctorCo = \ f g r ->
         pure {{AF}} f <*> (pure {{AF}} g <*> r)
           << lawCo (pure f) (pure g) r !!=
         pure {{AF}} (\ f g -> f o g) <*> pure f <*> pure g <*> r
           =!! cong (\ x -> x <*> pure g <*> r) (lawHom (\ f g -> f o g) f) >>
         pure {{AF}} (_o_ f) <*> pure g <*> r 
           =!! cong (\ x -> x <*> r) (lawHom (_o_ f) g) >>
         pure {{AF}} (f o g) <*> r
           <QED>
    }


vecApplicativeOKP : {n : Nat} -> ApplicativeOKP \ X -> Vec X n
vecApplicativeOKP = {!!}

--ApplicativeHomomorphisms

_-:>_ : forall (F G : Set -> Set) -> Set1
F -:> G = forall {X} -> F X -> G X

record AppHom  {F}{{AF : Applicative F}}{G}{{AG : Applicative G}}
               (k : F -:> G) : Set1 where
  field
    respPure  : forall {X}(x : X) -> k (pure x) == pure x
    respApp   : forall {S T}(f : F (S -> T))(s : F S) -> k (f <*> s) == k f <*> k s

monoidApplicativeHom :
  forall {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}
  (f : X -> Y){{hf : MonoidHom f}} ->
  AppHom {{monoidApplicative {{MX}}}} {{monoidApplicative {{MY}}}} f
monoidApplicativeHom f {{hf}} = record
  {  respPure  = \ x -> MonoidHom.respNeut hf
  ;  respApp   = MonoidHom.resp& hf
  }

--Show that a homomorphism from |F| to |G| induces applicative structure
--on their pointwise sum.

homSum :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
          (f : F -:> G) -> 
          Applicative \ X -> F X + G X
homSum {{AF}}{{AG}} f = {!!}

homSumOKP :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
             ApplicativeOKP F -> ApplicativeOKP G ->
             (f : F -:> G) -> AppHom f ->
             ApplicativeOKP _ {{homSum f}}
homSumOKP {{AF}}{{AG}} FOK GOK f homf = {!!}

-- traversable laws

record TraversableOKP F {{TF : Traversable F}} : Set1 where
  field
    lawId   :  forall  {X}(xs : F X) -> traverse id xs == xs
    lawCo   :  forall  {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                       {R S T}(g : S -> G T)(h : R -> H S)(rs : F R) ->
               let  EH : EndoFunctor H ; EH = applicativeEndoFunctor
               in   map{H} (traverse g) (traverse h rs)
                      ==
                    traverse{{TF}}{{applicativeComp AH AG}} (map{H} g o h) rs
    lawHom  :  forall {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                      (h : G -:> H){S T}(g : S -> G T) -> AppHom h ->
                      (ss : F S) ->
                      traverse (h o g) ss == h (traverse g ss)

-- fromNormal

Batch : Set -> Set -> Set
Batch X Y = Sg Nat \ n -> Vec X n -> Y


fromNormal :  forall {F}{{TF : Traversable F}} -> TraversableOKP F ->
              forall {X} -> <! normalT F !>N X -> F X
fromNormal {{TF}} tokf x = {!!}


-- fixpoints of normal functors

data Tree (N : Normal) : Set where
  <$_$> : <! N !>N (Tree N) -> Tree N

NatT : Normal
NatT = Two / 0 <?> 1

zeroT : Tree NatT
zeroT = <$ tt , <> $>

sucT : Tree NatT -> Tree NatT
sucT n = <$ ff , n , <> $>

NatInd :  forall {l}(P : Tree NatT -> Set l) ->
          P zeroT ->
          ((n : Tree NatT) -> P n -> P (sucT n)) ->
          (n : Tree NatT) -> P n
NatInd P z s n = {!!}

Dec : Set -> Set
Dec X = X + (X -> Zero)

eq? : (N : Normal)(sheq? : (s s' : Shape N) -> Dec (s == s')) ->
      (t t' : Tree N) -> Dec (t == t')
eq? N sheq? t t' = {!!}

