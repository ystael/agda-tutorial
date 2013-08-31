module Views where

open import Data.Nat

-- This is a _view_, a datatype that exists to expose information about its index value via
-- pattern matching on constructors.
data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd  : (k : ℕ) → Parity (1 + k * 2)
-- and here is the function that yields a view element at the desired index:
parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
-- here we use the pattern match of parity n to extract out the shape of n and insert it back
-- into the left using a dot-pattern
parity (suc .(k * 2))     | even k = odd k
parity (suc .(1 + k * 2)) | odd k  = even (suc k)

-- now we can divide natural numbers by two (truncating)
half : ℕ → ℕ
half n with parity n
half .(k * 2)     | even k = k
half .(1 + k * 2) | odd k  = k

open import Function
open import Data.List
open import Data.Bool

