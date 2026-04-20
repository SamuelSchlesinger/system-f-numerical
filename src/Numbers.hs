{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE RankNTypes         #-}

-- |
-- Module      : Numbers
-- Description : Church-encoded naturals, lists, and hyperoperations in System F.
-- Copyright   : (c) 2026 Samuel Schlesinger
-- License     : BSD-3-Clause
-- Maintainer  : sgschlesinger@gmail.com
-- Stability   : experimental
-- Portability : requires ImpredicativeTypes
--
-- A minimal System-F development of natural numbers, finite lists, and
-- the full /hyperoperation hierarchy/ — successor, addition,
-- multiplication, exponentiation, tetration, pentation, … — with no
-- recursion over data constructors and no inductive 'Data.Nat'-style
-- type. Every value here is a plain polymorphic function; all
-- computation is driven by polymorphic instantiation.
--
-- == The encoding
--
-- A natural number @n@ is represented as its /n-fold iteration
-- operator/: given any endofunction @f@ it returns @f . f . ... . f@
-- (@n@ copies). Because the same iterator works at every type we
-- package it as
--
-- @
-- type 'Nat' = forall x. (x -> x) -> (x -> x)
-- @
--
-- and recover every arithmetic operation by composing iterators.
--
-- == The hyperoperation trick
--
-- Each level of the hyperoperation hierarchy is obtained by /iterating
-- the previous level/, starting from @1@:
--
-- @
-- b^e        = iterate (mul b) e times from 1
-- b ↑↑ e     = iterate (exp b) e times from 1
-- b ↑↑↑ e    = iterate (tet b) e times from 1
-- @
--
-- The combinator 'hypSuc' captures that recurrence in one line:
--
-- @
-- hypSuc h b e = e \@'Nat' (h b) ('suc' 'zero')
-- @
--
-- Here @e@ is itself a Church numeral, so the type application
-- @e \@'Nat'@ instantiates its universally-quantified type variable at
-- the polymorphic type 'Nat' itself — an impredicative instantiation,
-- hence @ImpredicativeTypes@. 'exp', 'tet', and 'pent' become
-- one-liners over 'hypSuc'.
--
-- == Example
--
-- @
-- ghci> 'toInteger' ('exp'  ('fromInteger' 2) ('fromInteger' 10))
-- 1024
-- ghci> 'toInteger' ('tet'  ('fromInteger' 2) ('fromInteger' 4))
-- 65536          -- = 2^(2^(2^2))
-- ghci> 'toInteger' ('pent' ('fromInteger' 2) ('fromInteger' 3))
-- 65536          -- = 2 ↑↑ (2 ↑↑ 2) = 2 ↑↑ 4
-- @
--
-- == Caveat
--
-- 'toInteger' and 'fromInteger' are the straightforward System-F
-- definitions and are /not/ stack-safe for large @n@. Stack-safe
-- counterparts (@toIntegerStrict@, @fromIntegerStrict@) live in the
-- test suite.
--
module Numbers
  ( -- * Church-encoded naturals
    Nat
  , zero
  , suc
    -- * Marshalling naturals
  , toInteger
  , fromInteger
    -- * Arithmetic
  , BinOp
  , add
  , mul
  , exp
    -- * Hyper-arithmetic
  , hypSuc
  , tet
  , pent
    -- * Church-encoded finite lists
  , List
  , empty
  , cons
  , toList
  , fromList
  , append
  , lmul
  ) where

import Prelude hiding (fromInteger, toInteger, exp)

-- | Church-encoded natural numbers.
--
-- A 'Nat' is an @n@-fold iteration operator: given an endofunction
-- @f :: x -> x@ it returns the composition of @n@ copies of @f@. The
-- polymorphism in @x@ is what lets the same encoding drive every
-- operation in this module.
type Nat = forall x. (x -> x) -> (x -> x)

-- | The shape of a binary operation on a type @n@. Used as a convenient
-- alias for the arithmetic and list operations.
type BinOp n = n -> n -> n

-- | The natural number zero: iterating anything zero times is the
-- identity function.
--
-- @'toInteger' 'zero' == 0@.
zero :: Nat
zero = \_ -> id

-- | Successor. Iterating @f@ one more time than @n@ does is first
-- iterating @n@ times, then applying @f@ once more.
--
-- @'toInteger' ('suc' ('suc' 'zero')) == 2@.
suc :: Nat -> Nat
suc n = \f -> f . n f

-- | Convert a 'Nat' to a native 'Integer' by instantiating the iterator
-- at @Integer -> Integer@ with step @(+ 1)@ and starting value @0@.
--
-- This definition is /not/ stack-safe: it builds an @n@-deep thunk
-- chain. See the test suite for a strict, constant-stack variant.
toInteger :: Nat -> Integer
toInteger n = n (+ 1) 0

-- | Convert a non-negative 'Integer' to a 'Nat'. Calls 'error' on a
-- negative argument.
--
-- This definition is /not/ stack-safe: it recurses to depth @n@ on the
-- call stack. See the test suite for a tail-recursive variant.
fromInteger :: Integer -> Nat
fromInteger n
  | n == 0    = zero
  | n >  0    = suc (fromInteger (n - 1))
  | otherwise = error "Numbers.fromInteger: negative argument"

-- | Addition: apply @f@ @n@ times, then apply @f@ @m@ times. The total
-- is @n + m@ applications, encoded as composition of the two iterators.
add :: BinOp Nat
add n m = \f -> n f . m f

-- | Multiplication: iterating @f@ @m@ times is itself an endofunction;
-- apply that endofunction @n@ more times. The total is @n * m@
-- applications of @f@.
mul :: BinOp Nat
mul n m = \f -> n (m f)

-- | Successor in the /hyperoperation hierarchy/.
--
-- @hypSuc h b e@ iterates the unary operation @h b@ a total of @e@
-- times, starting from @1@:
--
-- @
-- hypSuc h b 0 = 1
-- hypSuc h b (e+1) = h b (hypSuc h b e)
-- @
--
-- If @h@ computes the @k@-th hyperoperation, @hypSuc h@ computes the
-- @(k+1)@-th:
--
-- @
-- 'hypSuc' 'mul' == 'exp'
-- 'hypSuc' 'exp' == 'tet'
-- 'hypSuc' 'tet' == 'pent'
-- @
--
-- The type application @e \@'Nat'@ is what requires
-- @ImpredicativeTypes@: it instantiates the universally-quantified
-- type variable of the Church numeral @e@ at the polymorphic type
-- 'Nat' itself.
hypSuc :: BinOp Nat -> BinOp Nat
hypSuc h = \b e -> e @Nat (h b) (suc zero)

-- | Exponentiation: @exp b e@ multiplies @b@ by itself @e@ times,
-- with @exp b 0 = 1@.
--
-- @'toInteger' ('exp' ('fromInteger' 2) ('fromInteger' 10)) == 1024@.
exp :: BinOp Nat
exp = hypSuc mul

-- | Tetration (Knuth @↑↑@): iterated exponentiation, producing a power
-- tower of height @e@.
--
-- @'toInteger' ('tet' ('fromInteger' 2) ('fromInteger' 4)) == 65536@
-- (which is @2^(2^(2^2))@).
tet :: BinOp Nat
tet = hypSuc exp

-- | Pentation (Knuth @↑↑↑@): iterated tetration. Grows stunningly fast;
-- even @pent 3 3@ is far beyond any computable 'Integer'.
pent :: BinOp Nat
pent = hypSuc tet

-- | Church-encoded finite lists. Directly analogous to 'Nat', with an
-- element argument threaded through each step of the fold: a
-- @'List' a@ is the operation that folds @f :: a -> x -> x@ across its
-- elements, starting from an initial seed.
type List a = forall x. (a -> x -> x) -> (x -> x)

-- | The empty list: the fold that ignores @f@ and returns its seed.
empty :: List a
empty _ x = x

-- | Prepend an element. Feed @a@ through @f@ first, then fold the rest.
cons :: a -> List a -> List a
cons a l = \f -> f a . l f

-- | Convert to a native Haskell list by folding with @(:)@ from @[]@.
toList :: List a -> [a]
toList l = l (:) []

-- | Convert a native Haskell list into a 'List'.
fromList :: [a] -> List a
fromList []       = empty
fromList (a : as) = cons a (fromList as)

-- | List concatenation. Exactly parallels 'add' on 'Nat': compose the
-- two folds.
append :: BinOp (List a)
append l1 l2 = \f -> l1 f . l2 f

-- | Cartesian product: @lmul xs ys@ enumerates every pair @(x, y)@
-- with @x@ from @xs@ and @y@ from @ys@, in lexicographic order.
-- Exactly parallels 'mul' on 'Nat': for each element on the left,
-- re-fold the right-hand list.
lmul :: List a -> List b -> List (a, b)
lmul l1 l2 = \f -> l1 (\a -> l2 (\b x -> f (a, b) x))
