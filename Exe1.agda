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


mult : {n : Nat} -> {X : Set} -> Vec (Vec X n) n -> Vec X n
mult {zero} vss = <>
mult {suc n} ((x , v) , vs) = x , mult (map tail  vs) where
  tail : {n : Nat} -> {X : Set} -> Vec X (suc n) -> Vec X n
  tail (x , xs) = xs

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

vtr :  forall {n G S T}{{_ : Applicative G}} ->
              (S -> G T) -> Vec S n -> G (Vec T n)
vtr {{aG}} f <>        = pure {{aG}} <>
vtr {{aG}} f (s , ss)  = pure {{aG}} _,_ <*> f s <*> vtr f ss

traversableVec : {n : Nat} -> Traversable \ X -> Vec X n
traversableVec = record { traverse = vtr }

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
listNMonoid = λ {X} → record { neut = (0 , <>); _&_ = monmult }

sumMonoid : Monoid Nat
sumMonoid = record { neut = 0; _&_ = _+Nat_ }

normalTraversable : (F : Normal) -> Traversable <! F !>N
normalTraversable F = record
  { traverse = \ {{aG}} f -> vv \ s xs -> pure {{aG}}  (_,_ s) <*> traverse f xs }

_oN_ : Normal -> Normal -> Normal
F oN (ShG / szG) = <! F !>N ShG / crush {{normalTraversable F}} szG

sizeT : forall {F}{{TF : Traversable F}}{X} -> F X -> Nat
sizeT {{TF}} = crush {{TF}} (\ _ -> 1)

normalT : forall F {{TF : Traversable F}} -> Normal
normalT F {{TF}} = F One / sizeT {{TF}}

shapeT : forall {F}{{TF : Traversable F}}{X} -> F X -> F One
shapeT {{TF}} = traverse {{TF}}  (\ _ -> <>)

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

-- Bounded arithmetic

shift : {n m : Nat} -> (i : Fin m) -> Fin (n +Nat m)
shift {zero} i = i
shift {suc n} i = suc (shift {n} i)

_+Fin_ : {m n : Nat} -> (i : Fin m) -> (j : Fin n) -> Fin (m +Nat n)
_+Fin_ {suc m} {n} zero  j = shift {suc m} {n} j
suc i +Fin j = suc (i +Fin j)

_*Fin_ : {m n : Nat} -> (i : Fin m) -> (j : Fin n) -> Fin (m *Nat n)
_*Fin_ {suc m} {zero} zero ()
_*Fin_ {suc m} {suc n} zero j = zero
suc i *Fin j = j +Fin (i *Fin j)

shiftRev : {m n : Nat} -> (i : Fin m) -> Fin (m +Nat n)
shiftRev zero = zero
shiftRev (suc i) = suc (shiftRev i)

shiftTimes : {m n : Nat} -> (i : Fin n) -> Fin ((suc m) *Nat n)
shiftTimes zero = zero
shiftTimes {zero} {suc n} (suc i) = suc (shiftRev i)
shiftTimes {suc m} {suc n} (suc i) = nudge (shift {n} {suc (n +Nat (m *Nat suc n))} (nudge (shiftRev i)))

slip : {m n : Nat} -> (i : Fin n) -> Fin (m +Nat n)
slip {zero} i = i
slip {suc m} i = suc (slip {m} i)

-- Some matrix operations

kroenecker : {m n : Nat} {X Y : Set} -> Vec X m -> Vec Y n
               -> Vec (Vec (X * Y) n) m
kroenecker xs ys = vmap (λ x → vmap (λ y → x , y) ys) xs

flatten : {m n : Nat} {X : Set} -> Vec (Vec X n) m -> Vec X (m *Nat n)
flatten {zero} <> = <>
flatten {suc m} (v , M) = v ++ flatten M

matrixMap : {m n : Nat} {X Y : Set} -> (X -> Y) -> Vec (Vec X n) m -> Vec (Vec Y n) m
matrixMap f = map (map f)


-- Encode pairs of bounded integers inside their bounded multiplication.
encode : {m n : Nat} -> Fin m -> Fin n -> Fin (m *Nat n)
encode zero j = shiftRev j
encode {suc m} {n} (suc i) j = slip {n} (encode i j)


swap : (F G : Normal) -> (F >< G) -N> (G >< F)
swap F G (sF , sG) = (sG , sF) , flatten swappedIndexMatrix where
  m   : Nat
  m   = size F sF
  n   : Nat
  n   = size G sG
  originalIndexMatrix : Vec (Vec (Fin m * Fin n) n) m
  originalIndexMatrix = kroenecker (upto (size F sF)) (upto (size G sG))
  swappedIndexMatrix : Vec (Vec (Fin (m *Nat n)) m) n
  swappedIndexMatrix = matrixMap (vv encode) (transpose originalIndexMatrix)



{----- Ask Conor why Agda can't figured out that in the first case
 ----- size F sF == 0.

drop : (F G : Normal) -> (F >< G) -N> (F oN G)
drop F G (sF , sG) with (size F sF)
drop F G (sF , sG) |    zero = (sF , {!!}) , {!!}
drop F G (sF , sG) |    suc n = {!!}

mydrop : (F G : Normal) -> (F >< G) -N> (F oN G)
mydrop F G (fst , snd) with (size F fst)
mydrop F G (fst , snd) | zero = (fst   , {!!}) , {!!}
mydrop F G (fst , snd) | suc q = {!!}
-}

drop : (F G : Normal) -> (F >< G) -N> (F oN G)
drop F G (sF , sG) = (sF , vec sG) , include {Shape G} {size G} {sG} (size F sF) where
  include : forall {X} -> {f : X -> Nat } -> {x : X} -> (n : Nat)
                       -> Vec (Fin (n *Nat (f x)))
                                   (vtr {n} {\ _ -> Nat} {X} {One}
                                            {{monoidApplicative}} f (vec x))
  include {X} {f} {x} zero  = <>
  include {X} {f} {x} (suc n) = map shiftRev (upto (f x)) ++ map (shift {f x}) (include {X} {f} {x} n)

---- SHEEEEEESH! That was hard!



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
    assoc = assoc++L
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
<>N = λ {X} → Monoid.neut listNMonoid

<_>N : {X : Set} -> (x : X) -> <! ListN !>N X
< x >N = 1 , (x , <>)

_++N_ : {X : Set} -> <! ListN !>N X -> <! ListN !>N X -> <! ListN !>N X
(zero , <>) ++N (n , ys) = n , ys
(suc m , (x , xs)) ++N (n , ys) with (m , xs) ++N (n , ys)
(suc m , (x , xs)) ++N (n , ys) | k , r  = suc k , (x , r)


symmetry :  {X : Set} {s t : X} -> s == t -> t == s
symmetry refl = refl

listNMonoidOK : {X : Set} -> MonoidOK (<! ListN !>N X)
listNMonoidOK {X} = record
  {
    absorbL = λ x → refl {X = <! ListN !>N X} ;
    absorbR = _++N<>;
    assoc = assoc++N
  } where
      _&&_ = Monoid._&_ listNMonoid

      _++N<> : (xs : <! ListN !>N X) -> xs & neut == xs
      (zero , <>) ++N<> = refl
      (suc n , (x , xs)) ++N<>
        = subst (symmetry ((n , xs) ++N<>))
                 (vv λ m ys → (suc m , (x , ys)) == (suc n , (x , xs)))
                 (refl {X = <! ListN !>N X})

      assoc++N : (xs ys zs : <! ListN !>N X) -> (xs && ys) && zs == xs && (ys && zs)
      assoc++N (zero , <>) ys zs = refl
      assoc++N (suc n , (x , xs)) ys zs = subst { X = <! ListN !>N X}
                                                (symmetry (assoc++N (n , xs) ys zs))
                                                (vv λ l us → (suc l) , (x , us) == (suc n , (x , xs)) && (ys && zs))
                                                refl
{-

Ask Conor: OK, but it's more ''natural'' to do induction over the
middle list, ys: first we show associativity for the one element list,
and then we move a single element left, abacus style.

I spent a lot of time trying to do that, but couldn't. See
listMonoidOK above.

-}

{-
\begin{exe}[a not inconsiderable problem]
Find out what goes wrong when you try to state associativity of vector |++|,
let alone prove it. What does it tell you about our |==| setup?
\end{exe}
-}

projProof : forall {X : Set} -> (f : X -> Set) -> (t s : Sg X f) -> (t == s)
                   -> Sg ( fst t == fst s)
                         (λ p -> subst p f (snd t) == snd s)
projProof f .s s refl = refl , refl


concatAssoc : {X : Set} {n m l : Nat} -> (xs : Vec X n) -> (ys : Vec X m) -> (zs : Vec X l) ->
              (subst (MonoidOK.assoc natMonoidOK n m l)
                     (Vec X)
                     ( ((xs ++ ys) ++ zs) )
              ) ==
              (xs ++ (ys ++ zs))
concatAssoc {X} {n} {m} {l} xs ys zs with MonoidOK.assoc listNMonoidOK (n , xs) (m , ys) (l , zs)
concatAssoc {X} {n} {m} {l} xs ys zs | r with projProof (Vec X) ((n +Nat m) +Nat l , (xs ++ ys) ++ zs) (n +Nat (m +Nat l) , xs ++ (ys ++ zs)) r
concatAssoc xs ys zs | r | pk , pus = {!!}

{- Ah... If proofs of equality were unique, I could deduce that
  pk == _.assoc+ .n .m .l and finish this proof.  Is there indeed no way to prove this? -}


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

vecEndoFunctorOKP : forall {n} -> EndoFunctorOKP λ X → Vec X n
vecEndoFunctorOKP {n} = record { endoFunctorId = idProof n; endoFunctorCo = functorialityProof n } where
  idProof : (n : Nat) -> {X : Set} (x : Vec X n) → vapp (vec (λ x₁ → x₁)) x == x
  idProof zero <> = refl
  idProof (suc m) (x , xs) rewrite idProof m xs = refl

  functorialityProof : (n : Nat) -> {R S T : Set} (f : S → T) (g : R → S) (x : Vec R n) →
                          vapp (vec f) (vapp (vec g) x) == vapp (vec (λ a → f (g a))) x
  functorialityProof zero f g <> = refl
  functorialityProof (suc m) f g (x , xs) rewrite functorialityProof m f g xs = refl

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
vecApplicativeOKP {n} =
  record {
    lawId = lawIdProof n ;
    lawCo = lawCoProof n ;
    lawHom = λ {S} {T} → lawHomProof n {S} {T};
    lawCom = lawComProof n
  } where

    lawIdProof : (n : Nat) → {X : Set} → (x : Vec X n) → pure {{applicativeVec}} id <*> x == x
    lawIdProof zero <> = refl
    lawIdProof (suc n) (x , xs) = cong (λ us → x , us) (lawIdProof n xs)

    lawCoProof : (n : Nat) -> {R S T : Set } → (f : Vec (S → T) n)
                                             → (g : Vec (R → S) n)
                                             → (r : Vec R n)
                      → pure {{applicativeVec}} (\ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)

    lawCoProof zero <> <> <> = refl
    lawCoProof (suc n) (f , fs) (g , gs) (r , rs)
      = cong (λ us → f (g r) , us) (lawCoProof n fs gs rs)

    lemma : forall {X} (x : X) -> vec {0} x == <>
    lemma x = refl

    lawHomProof : (n : Nat) → forall {S T}(f : S -> T)(s : S) ->
                     pure {{applicativeVec {n}}} f <*> pure s == pure (f s)
    lawHomProof zero {S} {T} f s =
      (vapp (vec f) (vec s))
        << (cong (λ v → vapp (vec f) v) (lemma s)) !!=
      <>
        =!! lemma (f s) >>
      vec (f s)
        <QED>
    lawHomProof (suc n) f s = cong (λ xs → f s , xs) (lawHomProof n f s)

    lawComProof : forall (n : Nat) {S T}(f : Vec (S -> T) n)(s : S) ->
                  f <*> pure s == pure {{applicativeVec}} (\ f -> f s) <*> f
    lawComProof zero <> s = refl
    lawComProof (suc n) (f , fs) s = cong (λ xs → f s , xs) (lawComProof n fs s)

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

coerce : forall {F G} {{AF : Applicative F}}{{AG : Applicative G}}
         (f : F -:> G) -> {X : Set} -> (F X + G X) -> G X
coerce f (tt , u) = f u
coerce f (ff , u) = u


homSum :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
          (f : F -:> G) ->
          Applicative \ X -> F X + G X
homSum {F} {G} {{AF}}{{AG}} f =
  record {
    pure = λ x → tt , (pure {{AF}} x);
    _<*>_ =  app
  } where
  app : {S T : Set} →
             Sg Two (F (S → T) <?> G (S → T)) →
             Sg Two (F S <?> G S) → Sg Two (F T <?> G T)
  app (tt , g) (tt , u) = tt , (g <*> u)
  app (tt , g) (ff , u) = ff , (f g <*> u )
  app (ff , g) (tt , u) = ff , (g <*> f u)
  app (ff , g) (ff , u) = ff , (g <*> u)

homSumOKP :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
             ApplicativeOKP F -> ApplicativeOKP G ->
             (f : F -:> G) -> AppHom f ->
             ApplicativeOKP _ {{homSum f}}
homSumOKP {F} {G} {{AF}}{{AG}} FOK GOK f homf =
  record {
    lawId = lawIdProof;
    lawCo = lawCoProof;
    lawHom = lawHomProof;
    lawCom = lawComProof
  } where
    lawIdProof : {X : Set} -> (x : F X + G X) ->
                    --(ff , pure {{AG}} (λ x₁ → x₁)) <*> (coerce f x)
                 _<*>_ {{homSum f}} (pure {{homSum f}} id) x == x
    lawIdProof (tt , u) = tt , (AF Applicative.<*> Applicative.pure AF (λ x → x)) u
                            =!! cong (_,_ tt) (ApplicativeOKP.lawId FOK u) >>
                          tt , u <QED>

    lawIdProof (ff , u) = ff , (AG Applicative.<*> f (Applicative.pure AF (λ x → x))) u
                             =!! cong (λ q → ff , (q <*> u)) (AppHom.respPure homf id) >>
                          ff , (AG Applicative.<*> Applicative.pure AG (λ x → x)) u
                             =!! cong (_,_ ff) (ApplicativeOKP.lawId GOK u) >>
                          ff , u
                             <QED>

    lawCoProof : {R S T : Set} (g : F (S → T) + G (S → T))
                   (h : F (R → S) + G (R → S)) (r : F R + G R) →
                   _<*>_ {{homSum f}}
                   ( _<*>_ {{homSum f}} (_<*>_ {{homSum f}} (pure {{homSum f}} (λ g h → g o h)) g) h)
                   r
                   == _<*>_ {{homSum f}} g (_<*>_ {{homSum f}} h r) -- (_<*>_ {{homSum f}} h r)
    lawCoProof (tt , g) (tt , h) (tt , r) = tt ,  _<*>_ {{AF}}
                                                        ( _<*>_ {{AF}} (_<*>_ {{AF}} (pure {{AF}} (λ g h → g o h)) g) h) r
                                              =!! cong (λ q → tt , q) (ApplicativeOKP.lawCo FOK g h r) >>
                                            tt , (AF Applicative.<*> g) ((AF Applicative.<*> h) r)
                                              <QED>
    lawCoProof (tt , g) (tt , h) (ff , r) = ff ,
                                              (AG Applicative.<*>
                                              f
                                              ((AF Applicative.<*>
                                              (AF Applicative.<*> Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))) g)
                                              h))
                                              r
                                                =!! cong (λ q → ff , (_<*>_ {{AG}} q r)) (AppHom.respApp homf ((_<*>_ {{AF}} (pure {{AF}} (λ g₁ g₂ a → g₁ (g₂ a))) g)) h) >>
                                                ff ,
                                                (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                f
                                                ((AF Applicative.<*> Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a)))
                                                g))
                                                (f h))
                                                r
                                                =!! cong (λ q → ff ,
                                                                     (AG Applicative.<*>
                                                                     (AG Applicative.<*>
                                                                     q) (f h))
                                                                     r)
                                                                     (AppHom.respApp homf (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))) g) >>
                                                ff , (AG Applicative.<*>
                                                       (AG Applicative.<*>
                                                         (AG Applicative.<*>
                                                           (f ((Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))))))
                                                           (f g))
                                                         (f h))
                                                       r
                                                   =!! cong (λ q → ff , (AG Applicative.<*>
                                                               (AG Applicative.<*>
                                                                 (AG Applicative.<*>
                                                                   q)
                                                                   (f g))
                                                                 (f h))
                                                               r)
                                                            (AppHom.respPure homf (λ g h → g o h) ) >>
                                                ff , (AG Applicative.<*>
                                                        (AG Applicative.<*>
                                                          (AG Applicative.<*>
                                                            Applicative.pure AG (λ g₁ g₂ a → g₁ (g₂ a)))
                                                            (f g))
                                                          (f h))
                                                        r
                                                  =!! cong (λ q → ff , q) ((ApplicativeOKP.lawCo GOK (f g) (f h) r)) >>
                                                ff , (AG Applicative.<*> f g) ((AG Applicative.<*> f h) r)
                                                  <QED>
    lawCoProof (tt , g) (ff , h) (tt , r) = ff ,
                                                 (AG Applicative.<*>
                                                   (AG Applicative.<*>
                                                     f
                                                     ((AF Applicative.<*>
                                                       Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a)))
                                                       g))
                                                     h)
                                                   (f r)
                                               =!! cong (λ q → ff ,
                                                            (AG Applicative.<*>
                                                              (AG Applicative.<*>
                                                                q)
                                                                h)
                                                              (f r))
                                                              (
                                                              AppHom.respApp homf
                                                              (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a)))
                                                              g) >>
                                                              ff ,
                                                              (AG Applicative.<*>
                                                              (AG Applicative.<*>
                                                              (AG Applicative.<*>
                                                              (f (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a)))))
                                                              (f g))
                                                              h)
                                                           (f r)
                                                   =!! cong (λ q →  ff ,
                                                                      (AG Applicative.<*>
                                                                        (AG Applicative.<*>
                                                                          (AG Applicative.<*>
                                                                            q)
                                                                            (f g))
                                                                          h)
                                                                        (f r))
                                                            (AppHom.respPure homf (λ g h  → g o h)) >>
                                               ff ,
                                                 (AG Applicative.<*>
                                                   (AG Applicative.<*>
                                                     (AG Applicative.<*>
                                                       Applicative.pure AG (λ g₁ g₂ a → g₁ (g₂ a)))
                                                       (f g))
                                                     h)
                                                   (f r)
                                                 =!! cong (λ q → ff , q) (ApplicativeOKP.lawCo GOK (f g) h (f r)) >>
                                               ff , (AG Applicative.<*> f g) ((AG Applicative.<*> h) (f r))
                                                 <QED>
    lawCoProof (tt , g) (ff , h) (ff , r) = ff ,
                                               (AG Applicative.<*>
                                                 (AG Applicative.<*>
                                                   f
                                                   ((AF Applicative.<*>
                                                     Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a)))
                                                     g))
                                                   h)
                                                 r
                                              =!! cong (λ q → ff ,
                                                                   (AG Applicative.<*>
                                                                     (AG Applicative.<*>
                                                                       q)
                                                                       h)
                                                                     r)
                                                       ( AppHom.respApp homf
                                                                        (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a)))
                                                                        g) >>
                                            ff ,
                                                 (AG Applicative.<*>
                                                   (AG Applicative.<*>
                                                     (AG Applicative.<*>
                                                       f
                                                       (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))))
                                                       (f g))
                                                     h)
                                                   r
                                              =!! cong (λ q →
                                                           ff ,
                                                             (AG Applicative.<*>
                                                               (AG Applicative.<*>
                                                                 (AG Applicative.<*>
                                                                   q)
                                                                   (f g))
                                                                 h)
                                                               r)
                                                               (AppHom.respPure homf
                                                                 (λ g₁ g₂ a → g₁ (g₂ a))) >>
                                            ff ,
                                                 (AG Applicative.<*>
                                                   (AG Applicative.<*>
                                                     (AG Applicative.<*>
                                                       Applicative.pure AG (λ g₁ g₂ a → g₁ (g₂ a)))
                                                       (f g))
                                                     h)
                                                   r
                                              =!! cong (λ q → ff , q) (ApplicativeOKP.lawCo GOK (f g) h r) >>
                                            ff , (AG Applicative.<*> f g) ((AG Applicative.<*> h) r) <QED>
    lawCoProof (ff , g) (tt , h) (tt , r) = ff ,
                                                 (AG Applicative.<*>
                                                   (AG Applicative.<*>
                                                     (AG Applicative.<*>
                                                       f (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))))
                                                     g)
                                                   (f h))
                                                 (f r)
                                              =!! cong (λ q →
                                                           ff ,
                                                             (AG Applicative.<*>
                                                               (AG Applicative.<*>
                                                                 (AG Applicative.<*>
                                                                   q)
                                                                   g)
                                                                 (f h))
                                                               (f r))
                                                       (AppHom.respPure homf (λ g h → g o h)) >>
                                            ff ,
                                              (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                  (AG Applicative.<*>
                                                    Applicative.pure AG (λ g₁ g₂ a → g₁ (g₂ a)))
                                                    g)
                                                  (f h))
                                                (f r)
                                              =!! cong (λ q → ff , q) (ApplicativeOKP.lawCo GOK g (f h) (f r)) >>
                                            ff , (AG Applicative.<*> g) ((AG Applicative.<*> f h) (f r))
                                              << cong (λ q → ff , (AG Applicative.<*> g) q )
                                                      (AppHom.respApp homf h r) !!=
                                            ff , (AG Applicative.<*> g) (f ((AF Applicative.<*> h) r)) <QED>
    lawCoProof (ff , g) (tt , h) (ff , r) = ff ,
                                              (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                  (AG Applicative.<*>
                                                    f (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))))
                                                    g)
                                                  (f h))
                                                r
                                              =!! cong (λ q →
                                                            ff ,
                                                              (AG Applicative.<*>
                                                                (AG Applicative.<*>
                                                                  (AG Applicative.<*>
                                                                    q)
                                                                    g)
                                                                  (f h))
                                                                r

                                                       )
                                                       (AppHom.respPure homf (λ g h → g o h)) >>
                                            ff ,
                                              (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                  (AG Applicative.<*>
                                                    Applicative.pure AG (λ g₁ g₂ a → g₁ (g₂ a)))
                                                    g)
                                                  (f h))
                                                r
                                              =!! cong (λ q → ff , q )
                                                       (ApplicativeOKP.lawCo GOK g (f h) r) >>
                                            ff , (AG Applicative.<*> g) ((AG Applicative.<*> f h) r) <QED>
    lawCoProof (ff , g) (ff , h) (tt , r) =
                                            ff ,
                                              (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                  (AG Applicative.<*>
                                                    f (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))))
                                                    g)
                                                  h)
                                              (f r)
                                              =!! cong (λ q → ff ,
                                                                (AG Applicative.<*>
                                                                  (AG Applicative.<*>
                                                                    (AG Applicative.<*>
                                                                      q)
                                                                      g)
                                                                    h)
                                                                  (f r)
                                                              )
                                                       (AppHom.respPure homf (λ g h → g o h)) >>
                                            ff ,
                                              (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                  (AG Applicative.<*>
                                                    Applicative.pure AG (λ g₁ g₂ a → g₁ (g₂ a)))
                                                    g)
                                                  h)
                                                (f r)
                                              =!! cong (λ q → ff , q)
                                                       (ApplicativeOKP.lawCo GOK g h (f r)) >>
                                            ff , (AG Applicative.<*> g) ((AG Applicative.<*> h) (f r)) <QED>
    lawCoProof (ff , g) (ff , h) (ff , r) = ff ,
                                              (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                  (AG Applicative.<*>
                                                    f
                                                      (Applicative.pure AF (λ g₁ g₂ a → g₁ (g₂ a))))
                                                    g)
                                                  h)
                                                r
                                              =!! cong (λ q →
                                                              ff ,
                                                                (AG Applicative.<*>
                                                                  (AG Applicative.<*>
                                                                    (AG Applicative.<*>
                                                                      q)
                                                                      g)
                                                                    h)
                                                                  r
                                                              )
                                                       (AppHom.respPure homf (λ g h → g o h)) >>
                                            ff ,
                                              (AG Applicative.<*>
                                                (AG Applicative.<*>
                                                  (AG Applicative.<*>
                                                    Applicative.pure AG (λ g₁ g₂ a → g₁ (g₂ a))) g)
                                                    h)
                                                  r
                                              =!! cong (λ q → ff , q) (ApplicativeOKP.lawCo GOK g h r) >>
                                            ff , (AG Applicative.<*> g) ((AG Applicative.<*> h) r) <QED>
                   {- FUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUUU----!!!
                                            That was long.

                                            Try to think of a shorter and more abstract way to go about
                                            it. Even just some kind of clever syntax to rid the boilerplate
                                            would be nice.

                   -}
    lawHomProof : {S T : Set} (g : S → T) (s : S) →
                   tt , (AF Applicative.<*> Applicative.pure AF g) (Applicative.pure AF s)
                   == tt , Applicative.pure AF (g s)
    lawHomProof g s = tt ,
                         (AF Applicative.<*> Applicative.pure AF g) (Applicative.pure AF s)
                        =!! cong (λ q → tt , q) (ApplicativeOKP.lawHom FOK g s) >>
                      tt , Applicative.pure AF (g s) <QED>
    lawComProof : {S T : Set} (g : Sg Two (F (S → T) <?> G (S → T))) (s : S) →
                      _<*>_ {{homSum f}} g (pure {{homSum f}} s) == _<*>_ {{homSum f}} (pure {{homSum f}} (\h -> h s)) g
    lawComProof (tt , g) s = tt , (AF Applicative.<*> g) (Applicative.pure AF s)
                               =!! cong (λ q → (tt , q)) (ApplicativeOKP.lawCom FOK g s) >>
                             tt , (AF Applicative.<*> Applicative.pure AF (λ f₁ → f₁ s)) g <QED>
    lawComProof (ff , g) s = ff , (AG Applicative.<*> g) (f (Applicative.pure AF s))
                               =!! cong (λ q → (ff , (AG Applicative.<*> g) q)) (AppHom.respPure homf s) >>
                             ff , (AG Applicative.<*> g) (Applicative.pure AG s)
                               =!! cong (λ q → ff , q) (ApplicativeOKP.lawCom GOK g s) >>
                             ff , (AG Applicative.<*> Applicative.pure AG (λ f₁ → f₁ s)) g
                               << cong (λ q → ff , _<*>_ {{AG}} q g) (AppHom.respPure homf (λ f₁ → f₁ s)) !!=
                             ff , (AG Applicative.<*> f (Applicative.pure AF (λ h → h s))) g <QED>

-- To Conor: The fact that respPure is typeset as resppure is confusing!!!!


-- traversable laws

record TraversableOKP F {{TF : Traversable F}} : Set1 where
  field
    lawId   :  forall  {X}(xs : F X) -> traverse {{TF}} id xs == xs
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

ABatch : {X : Set} -> Applicative  (Batch X)
ABatch {X} =
  record {
    pure = λ y → 0 , (λ x → y);
    _<*>_ = app
  } where
    app : {S T : Set} -> Batch X (S -> T) -> Batch X S -> Batch X T
    app (n , vs) (m , us) = (n +Nat m) , (λ ws → splitAndApply ws) where
      splitAndApply : (ws : Vec _ (n +Nat m)) -> _
      splitAndApply ws with concatSurjectivity {n} ws
      splitAndApply .(vi ++ ui) | from (vi , ui) = (vs vi) (us ui)

BatchOK : {X : Set} -> ApplicativeOKP (Batch X)
BatchOK {X} =
  record {
    lawId = lawIdProof;
    lawCo = {!lawCoProof!};
    lawHom = {!!};
    lawCom = {!!}
  } where
  lawIdProof : {X₁ : Set} (x : Sg Nat (λ n → Vec X n → X₁)) →
                   fst x , (λ ws → snd x ws) == x
  lawIdProof (n , ub) = refl

  lawCoProof : forall {R S T}(f : Batch X (S -> T))(g : Batch X (R -> S))(r : Batch X R) ->
               pure {{ABatch}} (\ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)
  lawCoProof (n , f) (m , g) (l , r) = {!!}


bar : forall {X} -> Vec X 1 -> X
bar (x , <>) = x
foo : forall {F} {{TF : Traversable F}} -> F One -> forall {X} -> Batch X (F X)
foo {F} {{TF}} sF {X} = traverse {F} {{TF}} {Batch X} {{ABatch}} (λ _ → 1 , bar) sF 

coherence : forall {F} {{TF : Traversable F}} {X} -> TraversableOKP F 
            -> (sF : F One) -> 
               fst (foo {F} {{TF}} sF {X}) == 
               Traversable.traverse {F} TF {λ _ → Nat} {One} {One} {{monoidApplicative}} (λ _ → 1) sF
coherence {F} {{TF}} {X} tokF u = 
   fst (Traversable.traverse TF (λ _ → 1 , bar) u) 
     << TraversableOKP.lawHom {F} {TF} tokF {Batch X} {{ABatch}} {λ _ → Nat} {{monoidApplicative}} fst (λ _ → 1 , bar) 
        (record { respPure = λ {X₁} x → refl
                ; respApp  = λ f s → refl }) u !!= 
   (Traversable.traverse TF {λ _ → Nat} {One {lzero}} {X}
     {{record { pure = λ {_} _ → 0; _<*>_ = λ {_} {_} → _+Nat_ }}}
     (λ a → 1) u)
     =!! {!!} >>
   (Traversable.traverse TF {λ _ → Nat} {One {lzero}} {One}
     {{record { pure = λ {_} _ → 0; _<*>_ = λ {_} {_} → _+Nat_ }}}
     (λ a → 1) u) <QED>
  


fromNormal :  forall {F}{{TF : Traversable F}} -> TraversableOKP F ->
              forall {X} -> <! normalT F !>N X -> F X
fromNormal {F} {{TF}} tokf {X} (sF , cF) with (coherence {F} {{TF}} {X} tokf sF) 
fromNormal {F} {{TF}} tokf {X} (sF , cF) | q with foo {F} {{TF}} sF {X} 
fromNormal {F} {{TF}} tokf {X} (sF , cF) | q | n , csF = csF (subst (symmetry q) (λ u → Vec X u) cF)
{-
with 
fromNormal {F} {{TF}} tokf {X} (sF , cF) | n , fcF = fcF (subst {!!} 
           (λ q → Vec X q) cF)
-}


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

--Dec : Set -> Set
--Dec X = X + (X -> Zero)

eq? : (N : Normal)(sheq? : (s s' : Shape N) -> Dec (s == s')) ->
      (t t' : Tree N) -> Dec (t == t')
eq? N sheq? t t' = {!!}
