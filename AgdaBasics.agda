module AgdaBasics where

-- basic inductive type
data Bool : Set where
  true : Bool
  false : Bool

-- definition by pattern matching
not : Bool -> Bool
not true  = false
not false = true

-- another basic inductive type
data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

-- infix operators
_+_ : Nat -> Nat -> Nat
zero   + n = n
succ m + n = succ (m + n)

_*_ : Nat -> Nat -> Nat
zero   * n = zero
succ m * n = n + (m * n)

-- don't care pattern
_or_ : Bool -> Bool -> Bool
false or x = x
true  or _ = true

-- multi-infix operator
if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then a else _ = a
if false then _ else b = b

-- fixity declarations
infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix   5 if_then_else_

-- cons lists
infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

-- explicit polymorphism parameter
identity : (A : Set) -> A -> A
identity A x = x

-- you can also eta expand
identity2 : (A : Set) -> A -> A
identity2 = λ A x -> x

-- dependent application with explicit parameters
apply : (A : Set)(B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
apply A B f x = f x

-- implicit polymorphism parameter
id : {A : Set} -> A -> A
id x = x

-- dependent composition with implicit parameters
_∘_ : {A : Set}{B : A -> Set}{C : (x : A) -> B x -> Set}
      (g : {x : A}(y : B x) -> C x y)(f : (x : A) -> B x)(x : A) -> C x (f x)
(g ∘ f) x = g (f x)

-- map over cons lists
map : {A B : Set} -> (A -> B) -> List A -> List B
map _ []        = []
map f (x :: xs) = f x :: map f xs

-- append over cons lists
_++_ : {A : Set} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

-- vectors of parametric type and given length
data Vec (A : Set) : Nat -> Set where
  []   : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (succ n)

-- head function, total when we insist that vector length is positive
head : {A : Set}{n : Nat} -> Vec A (succ n) -> A
head (x :: xs) = x

tail : {A : Set}{n : Nat} -> Vec A (succ n) -> Vec A n
tail (x :: xs) = xs

-- map over vectors, same definition modulo type signature
vmap : {A B : Set}{n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f []        = []
vmap f (x :: xs) = f x :: vmap f xs

-- vectors with explicit length parameter
data Vec2 (A : Set) : Nat -> Set where
  nil  : Vec2 A zero
  cons : (n : Nat) -> A -> Vec2 A n -> Vec2 A (succ n)

-- dot goes on a parameter that can be inferred from other binding instances in the pattern
-- so that every variable has exactly one binding instance not dotted
vmap2 : {A B : Set}(n : Nat) -> (A -> B) -> Vec2 A n -> Vec2 B n
vmap2 .zero     f nil           = nil
vmap2 .(succ n) f (cons n x xs) = cons n (f x) (vmap2 n f xs)

-- you can dot the other way, the rule is "exactly one binding instance of each identifier"
vmap3 : {A B : Set}(n : Nat) -> (A -> B) -> Vec2 A n -> Vec2 B n
vmap3 zero     f nil           = nil
vmap3 (succ n) f (cons .n x xs) = cons n (f x) (vmap3 n f xs)

-- type of proofs that the image of f contains a given element
data Image_∋_ {A B : Set}(f : A -> B) : B -> Set where
  -- the only way to prove it is to give manifestly the preimage
  im : (x : A) -> Image f ∋ f x

-- partial inverter for functions: given a proof that y is in the image of f, we can
-- extract the preimage
inv : {A B : Set}(f : A -> B)(y : B) -> Image f ∋ y -> A
-- f x is a parameter: given the proof (im x), the only type-correct application of this
-- function is at A B f (f x), so .(f x) is not the binding instance of x
inv f .(f x) (im x) = x

-- Fin n is the set of natural numbers < n, with a separate inductive constructor
data Fin : Nat -> Set where
  -- 0 < succ n for every n : Nat
  fzero : {n : Nat} -> Fin (succ n)
  -- if m < n then fsucc m < succ n
  fsucc : {n : Nat} -> Fin n -> Fin (succ n)

-- absurd (non-matching) patterns: given an element of an empty set we can produce anything
-- Fin zero is empty, manifest from datatype decl
magic : {A : Set} -> Fin zero -> A
magic ()

-- you can't use an absurd pattern if there is a valid constructor pattern for the type,
-- since telling whether the type is inhabited is undecidable
data Empty : Set where
  empty : Fin zero -> Empty -- can't happen, but "can" be constructed

magic' : {A : Set} -> Empty -> A
-- () can be used to match Fin zero, but not Empty
magic' (empty ())

-- list indexing function, total since the index is drawn from the type of possible indices
_!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
-- absurd pattern here since Fin zero is uninhabited
[] ! ()
(x :: xs) ! fzero   = x
(x :: xs) ! fsucc n = xs ! n

-- inverse of _!_: given a function index -> element, yield the list
tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
-- n is what you have to recurse over -- even though it's implicit!
tabulate {zero}   _ = []
-- f o fsucc is g : Fin n -> A, g i = f (fsucc i)
tabulate {succ n} f = (f fzero) :: tabulate (f ∘ fsucc)

-- the type of falsity has no constructors thus no inhabitants
data False : Set where
-- the type of truth could be defined as a type with a unique nullary constructor as in Coq
-- but if you define it as an empty record type it has a unique inhabitant record{}
record True : Set where
-- but you never actually have to name the inhabitant of the type
trivial : True
trivial = _

-- isTrue b is the type of proofs that b equals true
isTrue : Bool -> Set
isTrue true  = True
isTrue false = False

-- list indexing using explicit proofs of inboundness instead of dependent typing
-- standard < on Nat
_<_ : Nat -> Nat -> Bool
_      < zero   = false
zero   < succ n = true
succ m < succ n = m < n
-- function computing the length of a list
length : {A : Set} -> List A -> Nat
length []        = zero
length (x :: xs) = succ (length xs)
-- to find an element of a list, we need a proof that the index fits in the list
lookup : {A : Set}(xs : List A)(n : Nat) -> isTrue (n < length xs) -> A
-- this case can't happen (the type of proofs has no inhabitants)
lookup []        _        ()
-- the proof is immaterial here
lookup (x :: xs) zero     _  = x
-- this case uses the type checker to establish that a proof that (succ n) < length (x :: xs)
-- is also a proof that n < length xs
lookup (x :: xs) (succ n) pf = lookup xs n pf

-- propositions can be defined as inductive types directly, rather than being computed as
-- booleans and then reflected into inductive types using isTrue
-- this is the type of proofs that the left side equals the right side, parametric in the left
-- and only possessing a constructor for the same right
data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x
  -- (so x == y is an empty set, no constructors, if y is different from x)
-- similarly, inductive less-than-or-equal; the first argument cannot be a parameter here since
-- it needs to vary between different constructors
data _≤_ : Nat -> Nat -> Set where
  leq-zero : {n : Nat} -> zero ≤ n
  leq-succ : {m n : Nat} -> m ≤ n -> succ m ≤ succ n
-- now you can pattern match on proofs from this type, instead of having to reason back from
-- how a boolean value got to true; example, transitivity law for <=
leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
-- the left one is leq-zero {m}, the right one is leq-zero {n}
leq-trans leq-zero      _              = leq-zero
-- else l = succ l', m = succ m', n = succ n', pf is a proof that l' <= m', pf' is a proof that
-- m' <= n' (the right proof cannot be leq-zero either because m is not zero).  so transitivity
-- in recursion gives l' <= n' and we just apply the leq-succ constructor.
leq-trans (leq-succ pf) (leq-succ pf') = leq-succ (leq-trans pf pf')

-- use 'with' to introduce guard expressions in pattern matches, derived from arguments:
min : Nat -> Nat -> Nat
min x y with x < y
min x y | true  = x
min x y | false = y

-- list filtering function
-- the expression before the guard can be abbreviated when it is uninteresting
filter : {A : Set}(f : A -> Bool) -> List A -> List A
filter f [] = []
filter f (x :: xs) with f x
... | true  = x :: filter f xs
... | false = filter f xs

-- decidable equality: compares two numbers and returns a proof of equality or a proof of
-- disequality
-- here's an inductive type of proofs of natural number disequality
data _≠_ : Nat -> Nat -> Set where
  z≠s : {n : Nat} -> zero ≠ (succ n)
  s≠z : {n : Nat} -> (succ n) ≠ zero
  s≠s : {m n : Nat} -> m ≠ n -> (succ m) ≠ (succ n)
-- here's the disjoint union -- this is Coq {m == n} + {m != n}
data Equal? (n m : Nat) : Set where
  eq  : n == m -> Equal? n m
  neq : n ≠ m -> Equal? n m
-- and the proof function
equal? : (n m : Nat) -> Equal? n m
equal? zero      zero      = eq refl
equal? zero      (succ m') = neq z≠s
equal? (succ n') zero      = neq s≠z
equal? (succ n') (succ m') with equal? n' m'
-- Here we use the fact that refl is the only possible constructor under the eq to extract the
-- fact that n' == m' from the type checker and use a dot-pattern to pull it out.  In Coq this
-- would be a rewrite tactic.  If you didn't need to do this it could just be ... left of guard.
equal? (succ n') (succ .n') | eq refl = eq refl
equal? (succ n') (succ m')  | neq pf  = neq (s≠s pf)

-- let's prove that filter on a list returns a sublist
infix 20 _⊆_
-- here we use the "you figure out the type" forall construct for the implicit arguments.
-- this first one is exactly the same as giving implicit arguments {y : A}{xs ys : List A}
-- but forall is syntactic sugar for {y : _}{xs ys : _} and the typechecker will infer type.
-- because all arguments appear in the final term you can get the full type from point of use.
data _⊆_ {A : Set} : List A -> List A -> Set where
  stop : [] ⊆ []
  drop : ∀ {xs y ys} -> xs ⊆ ys ->      xs ⊆ y :: ys
  keep : ∀ {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys
-- now the theorem:
lem-filter : {A : Set}(p : A -> Bool)(xs : List A) -> filter p xs ⊆ xs
-- we know from the construction of filter that filter p [] = []
lem-filter p [] = stop
-- for this case, the implicit argument x is inferred by the required type of the left side
lem-filter p (x :: xs) with p x
... | true  = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)

-- You may want to with-abstract over something even if you're not going to match on it exactly
lem-plus-zero : (n : Nat) -> n + zero == n
lem-plus-zero zero = refl
-- || separate multiple guards.  Again there's no Coq-style rewrite so we can't directly apply
-- n' + zero == n' to rewrite the RHS of (succ n') + zero == succ n' to succ (n' + zero),
-- and the fact that the refl constructor has type x == x doesn't help because n' + zero does
-- not unify with n' syntactically.
-- Instead abstract out n + zero using a with-clause to give a rewrite weak enough for the
-- unifier to do it:
lem-plus-zero (succ n') with n' + zero | lem-plus-zero n'
-- the binding instance of n' here is the argument combined with the refl implicit arguments
-- i definitely don't understand what's going on here yet
... | .n' | refl = refl

-- More modules can be defined in a single file:
module M where
  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just    : A -> Maybe A
  -- this lifts a function A -> B to a function Maybe A -> B, given a default value
  maybe : {A B : Set} -> B -> (A -> B) -> Maybe A -> B
  maybe z f nothing  = z
  maybe z f (just x) = f x

-- names declared private are not visible outside the module
module A where
  private
    internal : Nat
    internal = zero

  exported : Nat -> Nat
  exported n = n + internal

-- module names act as namespace qualifiers in the usual way
mapMaybe1 : {A B : Set} -> (A -> B) -> M.Maybe A -> M.Maybe B
mapMaybe1 f M.nothing  = M.nothing
mapMaybe1 f (M.just x) = M.just (f x)

-- or you can open them locally
mapMaybe2 : {A B : Set} -> (A -> B) -> M.Maybe A -> M.Maybe B
mapMaybe2 f m = let open M in maybe nothing (just ∘ f) m

-- or globally
open M
mapMaybe3 : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe3 f m = maybe nothing (just ∘ f) m

-- you can also rename names from opened modules
open M hiding (maybe)
       -- the underscore here makes option a postfix type constructor
       renaming (Maybe to _option; nothing to none; just to some)
mapOption : {A B : Set} -> (A -> B) -> A option -> B option
mapOption f none     = none
mapOption f (some x) = some (f x)

-- Modules can be parameterized by types (NOT by modules, this is not an ML-style system)
module Sort (A : Set)(_<_ : A -> A -> Bool) where
  -- insert an element into a sorted list
  insert : A -> List A -> List A
  insert y [] = y :: []
  insert y (x :: xs) with x < y
  ... | true  = x :: insert y xs
  ... | false = y :: x :: xs

  -- insertion sort
  sort : List A -> List A
  sort []        = []
  sort (x :: xs) = insert x (sort xs)

-- From the outside, module parameters turn into initial arguments to all module fns
sort1 : (A : Set)(_<_ : A -> A -> Bool) -> List A -> List A
sort1 = Sort.sort

-- You can instantiate a module at particular types, which makes a new module
module SortNat = Sort Nat _<_
sort2 : List Nat -> List Nat
sort2 = SortNat.sort

-- Keyword 'public' exports some names from an inner module into an outer one
module Lists (A : Set)(_<_ : A -> A -> Bool) where
  open Sort A _<_ public
  minimum : List A -> Maybe A
  minimum xs with sort xs
  ... | []       = nothing
  ... | (x :: _) = just x
  -- now the exported names of Lists are insert, sort, minimum

-- yay record types
record Point : Set where
  field x y : Nat

mkPoint : Nat -> Nat -> Point
mkPoint a b = record{ x = a; y = b }

-- accessors are packed into a module named Point
getX : Point -> Nat
getX = Point.x

abs² : Point -> Nat
-- the Point module is parameterized by p so if you supply p at module instantiation then the
-- accessors become values not functions
abs² p = let open Point p in x * x + y * y

record Monad (M : Set -> Set) : Set1 where
  field
    return : {A : Set} -> A -> M A
    _>>=_ : {A B : Set} -> M A -> (A -> M B) -> M B
  -- You can add "methods" to a record type's module by mentioning them after the field decls
  mapM : {A B : Set} -> (A -> M B) -> List A -> M (List B)
  mapM f [] = return []
  mapM f (x :: xs) = f x       >>= λ mx ->
                     mapM f xs >>= λ mxs ->
                     return (mx :: mxs)

mapM' : {M : Set -> Set} -> Monad M -> {A B : Set} -> (A -> M B) -> List A -> M (List B)
-- the first argument here goes to instantiate the particular record being acted on by the
-- members of the module; it ends up acting something like a clojure method receiver
mapM' Mon f xs = Monad.mapM Mon f xs

-- Exercise 2.1. Matrix transposition

-- Model an n × m matrix (n rows, m columns) as a vector of m column vectors of length n
Matrix : Set -> Nat -> Nat -> Set
Matrix A n m = Vec (Vec A n) m

-- Constructor for a vector with the same value in each slot
vec : {n : Nat}{A : Set} -> A -> Vec A n
vec {zero}    _ = []
vec {succ n'} x = x :: vec {n'} x

-- vectorized application: [f1 ... fn] $ [x1 ... xn] = [f1.x1 ... fn.xn]
infixl 90 _$_
_$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
[] $ []               = []
(f :: fs) $ (x :: xs) = (f x) :: (fs $ xs)

-- Matrix transposition.  The transpose of T, a vector of m column vectors of length n, is a
-- vector of n column vectors of length m; the first one is made up of the first element of
-- each column of T, and so on.
transpose : ∀ {A n m} -> Matrix A n m -> Matrix A m n
-- m = 0 case (no columns), transposes to no rows, thus a vector of empty columns
transpose [] = vec []
-- n = 0 case (no rows), transposes to no columns, thus an empty vector
transpose ([] :: _) = []
-- m > 0, n > 0 case, here we have to pull the head of each column
-- what i really want here is an as-pattern rather than having to re-abstract once the
-- pattern match establishes that both m and n are successors
transpose ((x :: xs) :: cs) with ((x :: xs) :: cs)
... | t = vec head $ t :: transpose (vec tail $ t)

-- Exercise 2.2. Vector lookup

-- Proving that _!_ and tabulate are actually mutually inverse
lem-!-tab : ∀ {A n} (f : Fin n -> A)(i : Fin n) -> (tabulate f ! i) == f i
lem-!-tab f fzero = refl
lem-!-tab f (fsucc i') = lem-!-tab (f ∘ fsucc) i'

lem-tab-! : ∀ {A n} (xs : Vec A n) -> tabulate (_!_ xs) == xs
lem-tab-! [] = refl
lem-tab-! (x :: xs') with tabulate (_!_ xs') | lem-tab-! xs' 
... | .xs' | refl = refl

-- Exercise 2.3. Sublists

-- The sublist relation is reflexive and transitive
⊆-refl : {A : Set}{xs : List A} -> xs ⊆ xs
⊆-refl {xs = []} = stop
⊆-refl {xs = (x :: xs')} = keep ⊆-refl

⊆-trans : {A : Set}{xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
⊆-trans stop stop = stop
⊆-trans pf (drop pf') = drop (⊆-trans pf pf')
⊆-trans (drop pf) (keep pf') = drop (⊆-trans pf pf')
⊆-trans (keep pf) (keep pf') = keep (⊆-trans pf pf')

-- Type of sublists of a fixed list
data SubList {A : Set} : List A -> Set where
  []   : SubList []
  -- inclusion via consing x
  _::_ : ∀ x {xs} -> SubList xs -> SubList (x :: xs)
  -- inclusion via not consing x
  skip : ∀ {x xs} -> SubList xs -> SubList (x :: xs)

-- Extract the list of elements of a sublist
forget : {A : Set}{xs : List A} -> SubList xs -> List A
forget []        = []
forget (y :: ys) = y :: forget ys
forget (skip ys) = forget ys

-- and then establish that a sublist is a sublist
lem-forget : {A : Set}{xs : List A}(zs : SubList xs) -> forget zs ⊆ xs
lem-forget [] = stop
lem-forget (z :: zs') = keep (lem-forget zs')
lem-forget (skip zs') = drop (lem-forget zs')

-- Filtering yielding sublists
filter' : {A : Set} -> (A -> Bool) -> (xs : List A) -> SubList xs
filter' p [] = []
filter' p (x :: xs') with p x
... | true  = x :: (filter' p xs')
... | false = skip (filter' p xs')

-- Yield the complement, xs - ys
complement : {A : Set}{xs : List A}(ys : SubList xs) -> SubList xs
complement []             = []
complement (y :: ys')     = skip (complement ys')
complement (skip {x} ys') = x :: complement ys'

-- Yield all sublists of a given list
sublists : {A : Set}(xs : List A) -> List (SubList xs)
sublists []         = [] :: []
sublists (x :: xs') = (map (_::_ x) (sublists xs')) ++ (map skip (sublists xs'))
