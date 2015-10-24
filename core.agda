open import Agda.Primitive
module core where


  -- ----------------------------------------------------------------------
  -- functions

  -- _o_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
  -- g o f = \ x -> g (f x)
  -- infixr 10 _o_

  -- ----------------------------------------------------------------------
  -- identity type

  data _==_ {l : Level} {A : Set l} (M : A) : A -> Set l where
    Refl : M == M

  {-# BUILTIN EQUALITY _==_ #-}
  {-# BUILTIN REFL Refl #-}

  transport : {l1 : Level} {l2 : Level} {A : Set l1} (B : A -> Set l2)
              {a1 a2 : A} -> a1 == a2 -> (B a1 -> B a2)
  transport B Refl = λ x -> x

  ! : {l : Level} {A : Set l} {M N : A} -> M == N -> N == M
  ! Refl = Refl

  _∘_  : {l : Level} {A : Set l} {M N P : A}
      -> N == P -> M == N -> M == P
  β ∘ Refl = β

  ap :  {l1 l2 : Level} {A : Set l1} {B : Set l2} {M N : A}
       (f : A -> B) -> M == N -> (f M) == (f N)
  ap f Refl = Refl

  ap2 : {l1 l2 l3 : Level} {A : Set l1} {B : Set l2} {C : Set l3} {M N : A} {M' N' : B} (f : A -> B -> C) -> M == N -> M' == N' -> (f M M') == (f N N')
  ap2 f Refl Refl = Refl

  postulate
    -- function extensionality
    λ=  : {l1 l2 : Level} {A : Set l1} {B : A -> Set l2} {f g : (x : A) -> B x} -> ((x : A) -> (f x) == (g x)) -> f == g
    -- function extensionality for implicit functions
    λ=i  : {l1 l2 : Level} {A : Set l1} {B : A -> Set l2} {f g : {x : A} -> B x} -> ((x : A) -> (f {x}) == (g {x})) -> _==_ {_}{ {x : A} -> B x } f g

  private primitive primTrustMe : {l : Level} {A : Set l} {x y : A} -> x == y

  infixr 9 _==_

  infix  2 _∎
  infixr 2 _=〈_〉_

  _=〈_〉_ : {l : Level} {A : Set l} (x : A) {y z : A} -> x == y -> y == z -> x == z
  _ =〈 p1 〉 p2 = (p2 ∘ p1)

  _∎ : {l : Level} {A : Set l} (x : A) -> x == x
  _∎ _ = Refl

  -- ----------------------------------------------------------------------
  -- product types

  record Unit : Set where
    constructor <>

  record Σ {l1 l2 : Level} {A : Set l1} (B : A -> Set l2) : Set (l1 ⊔ l2) where
    constructor _,_
    field
      fst : A
      snd : B fst
  open Σ public

  infixr 0 _,_

  _×_ : {l1 l2 : Level} -> Set l1 -> Set l2 -> Set (l1 ⊔ l2)
  A × B = Σ (\ (_ : A) -> B)

  infixr 10 _×_

  -- ----------------------------------------------------------------------
  -- booleans

  data Bool : Set where
     True : Bool
     False : Bool

  {-# BUILTIN BOOL  Bool  #-}
  {-# BUILTIN TRUE  True  #-}
  {-# BUILTIN FALSE False #-}

  -- ----------------------------------------------------------------------
  -- order

  data Order : Set where
    Less : Order
    Equal : Order
    Greater : Order

  -- ----------------------------------------------------------------------
  -- sums

  data Void : Set where

  abort : {A : Set} -> Void -> A
  abort ()

  data Either (A B : Set) : Set where
    Inl : A -> Either A B
    Inr : B -> Either A B

  DecEq : Set -> Set
  DecEq A = (x y : A) -> Either (x == y) (x == y -> Void)

  -- ----------------------------------------------------------------------
  -- natural numbers

  module MyNat where
    data Nat : Set where
      Z : Nat
      S : Nat -> Nat

    -- let's you use numerals for Nat
    {-# BUILTIN NATURAL Nat #-}
    -- {-# BUILTIN SUC S #-}
    -- {-# BUILTIN ZERO Z #-}

    _+_ : Nat -> Nat -> Nat
    Z + n = n
    (S m) + n = S (m + n)

    max : Nat -> Nat -> Nat
    max Z n = n
    max m Z = m
    max (S m) (S n) = S (max m n)

    equal : Nat -> Nat -> Bool
    equal Z Z = True
    equal Z (S _) = False
    equal (S _) Z = False
    equal (S m) (S n) = equal m n

    compare : Nat -> Nat -> Order
    compare Z Z = Equal
    compare Z (S m) = Less
    compare (S n) Z = Greater
    compare (S n) (S m) = compare n m

  open MyNat public using (Nat ; Z ; S)


  -- ----------------------------------------------------------------------
  -- monad

  module Monad where

    record Monad : Set1 where
      field
        T : Set -> Set
        return : ∀ {A} -> A -> T A
        _>>=_  : ∀ {A B} -> T A -> (A -> T B) -> T B

  -- ----------------------------------------------------------------------
  -- options

  module MyMaybe where

    data Maybe {l : Level} (A : Set l) : Set l where
      Some : A -> Maybe A
      None : Maybe A

    Monad : Monad.Monad
    Monad = record { T = Maybe; return = Some; _>>=_ = (λ {None _ -> None; (Some v) f -> f v}) }

  open MyMaybe public using (Maybe;Some;None)

  -- ----------------------------------------------------------------------
  -- lists

  module MyList where
    data List {l : Level} (A : Set l) : Set l where
      []  : List A
      _::_ : A -> List A -> List A

    {-# COMPILED_DATA List [] [] (:) #-}
    {-# BUILTIN LIST List #-}
    {-# BUILTIN NIL [] #-}
    {-# BUILTIN CONS _::_ #-}

    infixr 99 _::_

    _++_ : {A : Set} -> List A -> List A -> List A
    [] ++ ys = ys
    (x :: xs) ++ ys = x :: (xs ++ ys)

    infixr 10 _++_

    map : {l1 l2 : Level} {A : Set l1} {B : Set l2} -> (A -> B) -> List A -> List B
    map f [] = []
    map f (x :: xs) = f x :: map f xs

    map-id : {l : Level} {A : Set l} (l : List A) -> map (\ (x : A) -> x) l == l
    map-id [] = Refl
    map-id (x :: l) with map (\ x -> x) l | map-id l
    ... | ._ | Refl = Refl

    module Uninformative where
      -- simply typed version
      peelOff : {A : Set} (eq : A -> A -> Bool) -> List A -> List A -> Maybe (List A)
      peelOff eq [] ys = Some ys
      peelOff eq (_ :: _) [] = None
      peelOff eq (x :: xs) (y :: ys) with eq x y
      ... | False = None
      ... | True = peelOff eq xs ys

    peelOff : {A : Set} (eq : DecEq A) -> (xs ys : List A) -> Maybe (Σ \ zs -> (xs ++ zs) == ys )
    peelOff eq [] ys = Some (ys , Refl)
    peelOff eq (_ :: _) [] = None
    peelOff eq (x :: xs) (y :: ys) with eq x y
    ... | Inr xyneq = None
    peelOff eq (x :: xs) (.x :: ys) | Inl Refl with peelOff eq xs ys
    peelOff eq (x :: xs) (.x :: .(xs ++ zs)) | Inl Refl | Some (zs , Refl) = Some (zs , Refl)
    ... | None = None

    [_] : {A : Set} -> A -> List A
    [ c ] = c :: []

    ++-assoc : ∀ {A} (l1 l2 l3 : List A) -> (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
    ++-assoc [] l2 l3 = Refl
    ++-assoc (x :: xs) l2 l3 = ap (_::_ x) (++-assoc xs l2 l3)

  open MyList public using (List ; [] ; _::_)


  -- ----------------------------------------------------------------------
  -- characters

  module Char where

    postulate {- Agda Primitive -}
      Char : Set

    {-# BUILTIN CHAR Char #-}
    {-# COMPILED_TYPE Char Char #-}

    private
     primitive
      primCharToNat    : Char -> Nat
      primCharEquality : Char -> Char -> Bool

    toNat : Char -> Nat
    toNat = primCharToNat

    equalb : Char -> Char -> Bool
    equalb = primCharEquality

    -- need to go outside the real language a little to give the primitives good types,
    -- but from the outside this should be safe
    equal : DecEq Char
    equal x y with equalb x y
    ... | True = Inl primTrustMe
    ... | False = Inr canthappen where
      postulate canthappen : _

  open Char public using (Char)

  -- ----------------------------------------------------------------------
  -- vectors

  module Vector where

    data Vec (A : Set) : Nat -> Set where
      []   : Vec A 0
      _::_ : ∀ {n} -> A -> Vec A n -> Vec A (S n)

    infixr 99 _::_

    Vec-elim : {A : Set} (P : {n : Nat} -> Vec A n -> Set)
               -> (P [])
               -> ({n : Nat} (x : A) (xs : Vec A n) -> P xs -> P (x :: xs))
               -> {n : Nat} (v : Vec A n) -> P v
    Vec-elim P n c [] = n
    Vec-elim P n c (y :: ys) = c y ys (Vec-elim P n c ys)

    fromList : {A : Set} -> List A -> Σ \n -> Vec A n
    fromList [] = _ , []
    fromList (x :: xs) = _ , x :: snd (fromList xs)

    toList : {A : Set} {n : Nat} -> Vec A n -> List A
    toList [] = []
    toList (x :: xs) = x :: (toList xs)

    toList' : {A : Set} -> (Σ \ n -> Vec A n) -> List A
    toList' (._ , []) = []
    toList' (._ , (x :: xs)) = x :: (toList' (_ , xs))

    to-from : {A : Set} (l : List A) -> toList' (fromList l) == l
    to-from [] = Refl
    to-from (x :: l) with toList' (fromList l) | to-from l
    to-from (x :: l) | .l | Refl = Refl

    from-to : {A : Set} (l : Σ \n -> Vec A n) -> fromList (toList' l) == l
    from-to (._ , []) = Refl
    from-to (._ , x :: l) with fromList (toList' (_ , l)) | from-to (_ , l)
    from-to (.(S n) , _::_ {n} x l) | .(n , l) | Refl = Refl




  data functor : Set1 where
    functor:constant : Set -> functor
    functor:identity : functor
    functor:list     : functor -> functor
    functor:product  : functor -> functor -> functor

  functor:apply : functor -> Set -> Set
  functor:apply (functor:constant A) _ = A
  functor:apply functor:identity a = a
  functor:apply (functor:list F) a = List (functor:apply F a)
  functor:apply (functor:product F1 F2) a
              = (functor:apply F1 a) × (functor:apply F2 a)

  module Example2 where
    F : functor
    F = (functor:product (functor:constant Nat)
                         functor:identity)
    x : (functor:apply F Bool)
    x = 1 , True

  functor:map : (F : functor) {A B : Set} ->
                (A -> B) ->
                functor:apply F A -> functor:apply F B
  functor:map (functor:constant A) f x = x
  functor:map functor:identity f x = f x
  functor:map (functor:list F) f x
            = MyList.map (functor:map F f) x
  functor:map (functor:product F1 F2) f x
            = {!!}
