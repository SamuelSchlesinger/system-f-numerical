{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE TypeApplications #-}
module Main (main) where

import Prelude hiding (fromInteger, toInteger, exp)

import Control.Exception (evaluate)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

import Numbers

-- Stack-safe Nat -> Integer.
--
-- The library's `toInteger n = n (+1) 0` builds an n-deep chain
-- `(+1) ((+1) ... 0)` whose outermost thunk forces inward to depth n.
-- Instantiating Nat at (Integer -> Integer) with a CPS step lets us
-- accumulate strictly while tail-calling through the chain, so stack
-- depth stays constant regardless of n.
toIntegerStrict :: Nat -> Integer
toIntegerStrict n = n step id 0
  where
    step :: (Integer -> Integer) -> (Integer -> Integer)
    step k = \acc -> k $! (acc + 1)

-- Stack-safe Integer -> Nat.
--
-- The library's `fromInteger` recurses to depth n on the call stack.
-- A tail-recursive accumulator avoids that; only the produced Nat is
-- a chain of n suc-closures in the heap.
fromIntegerStrict :: Integer -> Nat
fromIntegerStrict n0
  | n0 < 0    = error "fromIntegerStrict: negative"
  | otherwise = go n0 zero
  where
    go :: Integer -> Nat -> Nat
    go 0 acc = acc
    go k acc = go (k - 1) (suc acc)

-- Convenience: lift an Integer-typed binary op-check across the Nat encoding.
viaNat :: BinOp Nat -> Integer -> Integer -> Integer
viaNat op a b = toIntegerStrict (op (fromIntegerStrict a) (fromIntegerStrict b))

-- A small non-negative Integer generator. Bound is conservative so
-- properties stay fast even for the operations whose Nat encoding
-- forces O(value) reductions.
smallNat :: Gen Integer
smallNat = chooseInteger (0, 50)

tinyNat :: Gen Integer
tinyNat = chooseInteger (0, 10)

main :: IO ()
main = hspec $ do

  ----------------------------------------------------------------
  describe "zero / suc / round-trip" $ do

    it "zero encodes 0" $
      toIntegerStrict zero `shouldBe` 0

    it "suc zero encodes 1" $
      toIntegerStrict (suc zero) `shouldBe` 1

    it "suc (suc zero) encodes 2" $
      toIntegerStrict (suc (suc zero)) `shouldBe` 2

    prop "fromIntegerStrict / toIntegerStrict round-trip"
      $ forAll (chooseInteger (0, 1000))
      $ \n -> toIntegerStrict (fromIntegerStrict n) === n

    prop "library fromInteger / toInteger agree on small values"
      $ forAll (chooseInteger (0, 100))
      $ \n -> toInteger (fromInteger n) === n

    prop "library and strict converters agree"
      $ forAll (chooseInteger (0, 100))
      $ \n -> toIntegerStrict (fromInteger n)
              === toInteger (fromIntegerStrict n)

    it "library fromInteger errors on negatives" $
      evaluate (fromInteger (-1) :: Nat) `shouldThrow` anyErrorCall

    it "fromIntegerStrict errors on negatives" $
      evaluate (fromIntegerStrict (-1) :: Nat) `shouldThrow` anyErrorCall

  ----------------------------------------------------------------
  describe "addition (add)" $ do

    it "0 + 0 = 0"  $ viaNat add 0 0 `shouldBe` 0
    it "0 + 5 = 5"  $ viaNat add 0 5 `shouldBe` 5
    it "5 + 0 = 5"  $ viaNat add 5 0 `shouldBe` 5
    it "3 + 4 = 7"  $ viaNat add 3 4 `shouldBe` 7
    it "9 + 16 = 25" $ viaNat add 9 16 `shouldBe` 25

    prop "matches Integer (+)" $
      forAll smallNat $ \a ->
      forAll smallNat $ \b ->
        viaNat add a b === a + b

    prop "left identity (zero)" $
      forAll smallNat $ \a ->
        toIntegerStrict (add zero (fromIntegerStrict a)) === a

    prop "right identity (zero)" $
      forAll smallNat $ \a ->
        toIntegerStrict (add (fromIntegerStrict a) zero) === a

    prop "commutative" $
      forAll smallNat $ \a ->
      forAll smallNat $ \b ->
        viaNat add a b === viaNat add b a

    prop "associative" $
      forAll tinyNat $ \a ->
      forAll tinyNat $ \b ->
      forAll tinyNat $ \c ->
        let na = fromIntegerStrict a
            nb = fromIntegerStrict b
            nc = fromIntegerStrict c
        in toIntegerStrict (add na (add nb nc))
           === toIntegerStrict (add (add na nb) nc)

    prop "suc commutes with add: suc (a + b) = suc a + b" $
      forAll smallNat $ \a ->
      forAll smallNat $ \b ->
        let na = fromIntegerStrict a
            nb = fromIntegerStrict b
        in toIntegerStrict (suc (add na nb))
           === toIntegerStrict (add (suc na) nb)

  ----------------------------------------------------------------
  describe "multiplication (mul)" $ do

    it "0 * 0 = 0"   $ viaNat mul 0 0  `shouldBe` 0
    it "0 * 7 = 0"   $ viaNat mul 0 7  `shouldBe` 0
    it "7 * 0 = 0"   $ viaNat mul 7 0  `shouldBe` 0
    it "1 * 9 = 9"   $ viaNat mul 1 9  `shouldBe` 9
    it "9 * 1 = 9"   $ viaNat mul 9 1  `shouldBe` 9
    it "3 * 4 = 12"  $ viaNat mul 3 4  `shouldBe` 12
    it "6 * 7 = 42"  $ viaNat mul 6 7  `shouldBe` 42
    it "12 * 12 = 144" $ viaNat mul 12 12 `shouldBe` 144

    prop "matches Integer (*)" $
      forAll tinyNat $ \a ->
      forAll tinyNat $ \b ->
        viaNat mul a b === a * b

    prop "left absorbing (zero)" $
      forAll smallNat $ \a ->
        toIntegerStrict (mul zero (fromIntegerStrict a)) === 0

    prop "right absorbing (zero)" $
      forAll smallNat $ \a ->
        toIntegerStrict (mul (fromIntegerStrict a) zero) === 0

    prop "left identity (one)" $
      forAll smallNat $ \a ->
        toIntegerStrict (mul (suc zero) (fromIntegerStrict a)) === a

    prop "right identity (one)" $
      forAll smallNat $ \a ->
        toIntegerStrict (mul (fromIntegerStrict a) (suc zero)) === a

    prop "commutative" $
      forAll tinyNat $ \a ->
      forAll tinyNat $ \b ->
        viaNat mul a b === viaNat mul b a

    prop "associative" $
      forAll (chooseInteger (0, 6)) $ \a ->
      forAll (chooseInteger (0, 6)) $ \b ->
      forAll (chooseInteger (0, 6)) $ \c ->
        let na = fromIntegerStrict a
            nb = fromIntegerStrict b
            nc = fromIntegerStrict c
        in toIntegerStrict (mul na (mul nb nc))
           === toIntegerStrict (mul (mul na nb) nc)

    prop "left distributive: a*(b+c) = a*b + a*c" $
      forAll (chooseInteger (0, 6)) $ \a ->
      forAll (chooseInteger (0, 6)) $ \b ->
      forAll (chooseInteger (0, 6)) $ \c ->
        let na = fromIntegerStrict a
            nb = fromIntegerStrict b
            nc = fromIntegerStrict c
        in toIntegerStrict (mul na (add nb nc))
           === toIntegerStrict (add (mul na nb) (mul na nc))

    prop "right distributive: (a+b)*c = a*c + b*c" $
      forAll (chooseInteger (0, 6)) $ \a ->
      forAll (chooseInteger (0, 6)) $ \b ->
      forAll (chooseInteger (0, 6)) $ \c ->
        let na = fromIntegerStrict a
            nb = fromIntegerStrict b
            nc = fromIntegerStrict c
        in toIntegerStrict (mul (add na nb) nc)
           === toIntegerStrict (add (mul na nc) (mul nb nc))

  ----------------------------------------------------------------
  describe "exponentiation (exp)" $ do

    -- Edge cases for the exponent / base.
    it "n^0 = 1 for n = 0"  $ viaNat exp 0 0 `shouldBe` 1
    it "n^0 = 1 for n = 5"  $ viaNat exp 5 0 `shouldBe` 1
    it "n^1 = n for n = 0"  $ viaNat exp 0 1 `shouldBe` 0
    it "n^1 = n for n = 7"  $ viaNat exp 7 1 `shouldBe` 7
    it "1^n = 1 for n = 0"  $ viaNat exp 1 0 `shouldBe` 1
    it "1^n = 1 for n = 9"  $ viaNat exp 1 9 `shouldBe` 1
    it "0^n = 0 for n >= 1" $ do
      viaNat exp 0 1 `shouldBe` 0
      viaNat exp 0 4 `shouldBe` 0

    it "2^3 = 8"     $ viaNat exp 2 3 `shouldBe` 8
    it "3^3 = 27"    $ viaNat exp 3 3 `shouldBe` 27
    it "2^5 = 32"    $ viaNat exp 2 5 `shouldBe` 32
    it "5^2 = 25"    $ viaNat exp 5 2 `shouldBe` 25
    it "2^10 = 1024" $ viaNat exp 2 10 `shouldBe` 1024
    it "2^16 = 65536" $ viaNat exp 2 16 `shouldBe` 65536

    prop "matches Integer (^)" $
      forAll (chooseInteger (0, 6)) $ \a ->
      forAll (chooseInteger (0, 4)) $ \b ->
        viaNat exp a b === a ^ b

    prop "exp distributes over add in the exponent: b^(x+y) = b^x * b^y" $
      forAll (chooseInteger (1, 4)) $ \b ->
      forAll (chooseInteger (0, 4)) $ \x ->
      forAll (chooseInteger (0, 4)) $ \y ->
        let nb = fromIntegerStrict b
            nx = fromIntegerStrict x
            ny = fromIntegerStrict y
        in toIntegerStrict (exp nb (add nx ny))
           === toIntegerStrict (mul (exp nb nx) (exp nb ny))

  ----------------------------------------------------------------
  describe "tetration (tet)" $ do

    -- hypSuc h b 0 = (suc zero), so tet n 0 = 1 always (incl. n=0).
    it "tet 0 0 = 1" $ viaNat tet 0 0 `shouldBe` 1
    it "tet 2 0 = 1" $ viaNat tet 2 0 `shouldBe` 1
    it "tet 7 0 = 1" $ viaNat tet 7 0 `shouldBe` 1

    -- tet n 1 = exp n 1 = n.
    it "tet 0 1 = 0" $ viaNat tet 0 1 `shouldBe` 0
    it "tet 1 1 = 1" $ viaNat tet 1 1 `shouldBe` 1
    it "tet 2 1 = 2" $ viaNat tet 2 1 `shouldBe` 2
    it "tet 5 1 = 5" $ viaNat tet 5 1 `shouldBe` 5

    -- tet 1 n = 1 for n >= 1.
    it "tet 1 2 = 1" $ viaNat tet 1 2 `shouldBe` 1
    it "tet 1 9 = 1" $ viaNat tet 1 9 `shouldBe` 1

    -- Honest power-tower values.
    it "tet 2 2 = 2^2 = 4"            $ viaNat tet 2 2 `shouldBe` 4
    it "tet 2 3 = 2^(2^2) = 16"       $ viaNat tet 2 3 `shouldBe` 16
    it "tet 2 4 = 2^(2^(2^2)) = 65536" $ viaNat tet 2 4 `shouldBe` 65536
    it "tet 3 2 = 3^3 = 27"           $ viaNat tet 3 2 `shouldBe` 27
    it "tet 4 2 = 4^4 = 256"          $ viaNat tet 4 2 `shouldBe` 256
    it "tet 5 2 = 5^5 = 3125"         $ viaNat tet 5 2 `shouldBe` 3125
    it "tet 6 2 = 6^6 = 46656"        $ viaNat tet 6 2 `shouldBe` 46656
    it "tet 7 2 = 7^7 = 823543"       $ viaNat tet 7 2 `shouldBe` 823543

    -- Recurrence: tet b (e+1) = exp b (tet b e). Vet by computing both
    -- sides independently for the (b, e) pairs we can afford.
    it "tet recurrence: tet 2 3 = exp 2 (tet 2 2)" $
      viaNat tet 2 3 `shouldBe` viaNat exp 2 (viaNat tet 2 2)
    it "tet recurrence: tet 2 4 = exp 2 (tet 2 3)" $
      viaNat tet 2 4 `shouldBe` viaNat exp 2 (viaNat tet 2 3)
    it "tet recurrence: tet 3 2 = exp 3 (tet 3 1)" $
      viaNat tet 3 2 `shouldBe` viaNat exp 3 (viaNat tet 3 1)
    it "tet recurrence: tet 4 2 = exp 4 (tet 4 1)" $
      viaNat tet 4 2 `shouldBe` viaNat exp 4 (viaNat tet 4 1)

  ----------------------------------------------------------------
  describe "pentation (pent)" $ do

    -- pent n 0 = 1.
    it "pent 0 0 = 1" $ viaNat pent 0 0 `shouldBe` 1
    it "pent 2 0 = 1" $ viaNat pent 2 0 `shouldBe` 1
    it "pent 9 0 = 1" $ viaNat pent 9 0 `shouldBe` 1

    -- pent n 1 = tet n 1 = n.
    it "pent 0 1 = 0" $ viaNat pent 0 1 `shouldBe` 0
    it "pent 2 1 = 2" $ viaNat pent 2 1 `shouldBe` 2
    it "pent 5 1 = 5" $ viaNat pent 5 1 `shouldBe` 5

    -- pent 1 n = 1.
    it "pent 1 2 = 1" $ viaNat pent 1 2 `shouldBe` 1
    it "pent 1 5 = 1" $ viaNat pent 1 5 `shouldBe` 1

    -- pent 2 2 = tet 2 (pent 2 1) = tet 2 2 = 4.
    it "pent 2 2 = 4" $ viaNat pent 2 2 `shouldBe` 4

    -- pent 2 3 = tet 2 (pent 2 2) = tet 2 4 = 65536.
    it "pent 2 3 = 65536" $ viaNat pent 2 3 `shouldBe` 65536

  ----------------------------------------------------------------
  -- Pentation is the operation most likely to harbour a subtle bug,
  -- since each step explodes super-exponentially. We vet it at every
  -- small (base, exponent) pair we can afford by checking values
  -- against an independently-derived expectation, then by checking
  -- the definitional recurrence  pent b (e+1) = tet b (pent b e).
  describe "pentation small-value vetting" $ do

    -- pent 0 n alternates 1,0,1,0,... because tet 0 0 = 1, tet 0 1 = 0.
    it "pent 0 0..6 alternates 1,0,1,0,1,0,1" $
      map (viaNat pent 0) [0,1,2,3,4,5,6]
        `shouldBe` [1,0,1,0,1,0,1]

    -- pent 1 n = 1 for every n.
    it "pent 1 0..7 are all 1" $
      map (viaNat pent 1) [0,1,2,3,4,5,6,7]
        `shouldBe` replicate 8 1

    -- pent n 0 = 1 for every n  (the e=0 base case in hypSuc).
    it "pent n 0 = 1 for n in 0..8" $
      map (\n -> viaNat pent n 0) [0,1,2,3,4,5,6,7,8]
        `shouldBe` replicate 9 1

    -- pent n 1 = tet n 1 = n  (single tetration step).
    it "pent n 1 = n for n in 0..8" $
      map (\n -> viaNat pent n 1) [0,1,2,3,4,5,6,7,8]
        `shouldBe` [0,1,2,3,4,5,6,7,8]

    -- pent b 2 = tet b (tet b 1) = tet b b. Cross-check both sides.
    it "pent 0 2 = tet 0 0 = 1" $ do
      viaNat pent 0 2 `shouldBe` 1
      viaNat pent 0 2 `shouldBe` viaNat tet 0 0
    it "pent 1 2 = tet 1 1 = 1" $ do
      viaNat pent 1 2 `shouldBe` 1
      viaNat pent 1 2 `shouldBe` viaNat tet 1 1
    it "pent 2 2 = tet 2 2 = 4" $ do
      viaNat pent 2 2 `shouldBe` 4
      viaNat pent 2 2 `shouldBe` viaNat tet 2 2

    -- pent b 3 = tet b (pent b 2). Check at b = 0, 1, 2.
    it "pent 0 3 = tet 0 (pent 0 2) = tet 0 1 = 0" $ do
      viaNat pent 0 3 `shouldBe` 0
      viaNat pent 0 3 `shouldBe` viaNat tet 0 (viaNat pent 0 2)
    it "pent 1 3 = tet 1 (pent 1 2) = tet 1 1 = 1" $ do
      viaNat pent 1 3 `shouldBe` 1
      viaNat pent 1 3 `shouldBe` viaNat tet 1 (viaNat pent 1 2)
    it "pent 2 3 = tet 2 (pent 2 2) = tet 2 4 = 65536" $ do
      viaNat pent 2 3 `shouldBe` 65536
      viaNat pent 2 3 `shouldBe` viaNat tet 2 (viaNat pent 2 2)

    -- The full recurrence pent b (e+1) = tet b (pent b e),
    -- exercised on every (b, e) we can compute.
    it "pent 0 (e+1) = tet 0 (pent 0 e) for e in 0..5" $
      mapM_
        (\e -> viaNat pent 0 (e+1)
                 `shouldBe` viaNat tet 0 (viaNat pent 0 e))
        [0,1,2,3,4,5]
    it "pent 1 (e+1) = tet 1 (pent 1 e) for e in 0..5" $
      mapM_
        (\e -> viaNat pent 1 (e+1)
                 `shouldBe` viaNat tet 1 (viaNat pent 1 e))
        [0,1,2,3,4,5]
    it "pent 2 (e+1) = tet 2 (pent 2 e) for e in 0..2" $
      mapM_
        (\e -> viaNat pent 2 (e+1)
                 `shouldBe` viaNat tet 2 (viaNat pent 2 e))
        [0,1,2]

    -- A few mixed sanity checks at e = 1.
    it "pent 3 1 = 3"  $ viaNat pent 3 1 `shouldBe` 3
    it "pent 9 1 = 9"  $ viaNat pent 9 1 `shouldBe` 9
    it "pent 12 1 = 12" $ viaNat pent 12 1 `shouldBe` 12

  ----------------------------------------------------------------
  describe "cross-operation consistency" $ do

    -- mul a b == add a (... a) b times == n-fold add of a.
    prop "mul a b agrees with iterated add" $
      forAll tinyNat $ \a ->
      forAll tinyNat $ \b ->
        let na = fromIntegerStrict a
            nb = fromIntegerStrict b
        in toIntegerStrict (mul na nb)
           === toIntegerStrict (nb (add na) zero)

    -- exp a b == iterated mul of a, b times.
    prop "exp a b agrees with iterated mul (b >= 1, a >= 1)" $
      forAll (chooseInteger (1, 5)) $ \a ->
      forAll (chooseInteger (1, 4)) $ \b ->
        let na = fromIntegerStrict a
            nb = fromIntegerStrict b
        in toIntegerStrict (exp na nb)
           === toIntegerStrict (nb (mul na) (suc zero))

  ----------------------------------------------------------------
  -- Generators for List tests. We `resize` to keep Cartesian-product
  -- sizes (|xs| * |ys|) bounded, since `lmul` builds the full product.
  let smallList :: Gen [Int]
      smallList = resize 30 (listOf (chooseInt (-50, 50)))

      tinyList :: Gen [Int]
      tinyList  = resize 10 (listOf (chooseInt (-20, 20)))

  ----------------------------------------------------------------
  describe "empty / cons / round-trip" $ do

    it "toList empty == []" $
      toList (empty :: List Int) `shouldBe` []

    it "toList (cons 1 empty) == [1]" $
      toList (cons (1 :: Int) empty) `shouldBe` [1]

    it "toList (cons 1 (cons 2 (cons 3 empty))) == [1,2,3]" $
      toList (cons (1 :: Int) (cons 2 (cons 3 empty))) `shouldBe` [1,2,3]

    it "toList (fromList []) == []" $
      toList (fromList ([] :: [Int])) `shouldBe` []

    prop "fromList / toList round-trip" $
      forAll smallList $ \xs ->
        toList (fromList xs) === xs

    prop "cons matches (:) on the round-trip" $
      forAll (chooseInt (-50, 50)) $ \x ->
      forAll smallList $ \xs ->
        toList (cons x (fromList xs)) === x : xs

  ----------------------------------------------------------------
  describe "append" $ do

    it "append empty empty == []" $
      toList (append (empty :: List Int) empty) `shouldBe` []

    it "append empty [1,2] == [1,2]" $
      toList (append empty (fromList [1 :: Int, 2])) `shouldBe` [1, 2]

    it "append [1,2] empty == [1,2]" $
      toList (append (fromList [1 :: Int, 2]) empty) `shouldBe` [1, 2]

    it "append [1,2] [3,4,5] == [1,2,3,4,5]" $
      toList (append (fromList [1 :: Int, 2]) (fromList [3, 4, 5]))
        `shouldBe` [1, 2, 3, 4, 5]

    prop "matches Prelude (++)" $
      forAll smallList $ \xs ->
      forAll smallList $ \ys ->
        toList (append (fromList xs) (fromList ys)) === xs ++ ys

    prop "left identity (empty)" $
      forAll smallList $ \xs ->
        toList (append empty (fromList xs)) === xs

    prop "right identity (empty)" $
      forAll smallList $ \xs ->
        toList (append (fromList xs) empty) === xs

    prop "associative" $
      forAll tinyList $ \xs ->
      forAll tinyList $ \ys ->
      forAll tinyList $ \zs ->
        toList (append (fromList xs) (append (fromList ys) (fromList zs)))
          === toList (append (append (fromList xs) (fromList ys)) (fromList zs))

  ----------------------------------------------------------------
  describe "lmul (Cartesian product)" $ do

    it "lmul empty empty == []" $
      toList (lmul (empty :: List Int) (empty :: List Int)) `shouldBe` []

    it "lmul empty [1,2] == []" $
      toList (lmul (empty :: List Int) (fromList [1 :: Int, 2]))
        `shouldBe` []

    it "lmul [1,2] empty == []" $
      toList (lmul (fromList [1 :: Int, 2]) (empty :: List Int))
        `shouldBe` []

    it "lmul [1] ['a','b'] == [(1,'a'),(1,'b')]" $
      toList (lmul (fromList [1 :: Int]) (fromList ['a', 'b']))
        `shouldBe` [(1, 'a'), (1, 'b')]

    it "lmul [1,2] ['a','b'] == [(1,a),(1,b),(2,a),(2,b)]" $
      toList (lmul (fromList [1 :: Int, 2]) (fromList ['a', 'b']))
        `shouldBe` [(1,'a'), (1,'b'), (2,'a'), (2,'b')]

    it "lmul [1,2,3] ['a','b'] enumerates lex-order pairs" $
      toList (lmul (fromList [1 :: Int, 2, 3]) (fromList ['a', 'b']))
        `shouldBe` [(1,'a'),(1,'b'),(2,'a'),(2,'b'),(3,'a'),(3,'b')]

    prop "matches the list-comprehension Cartesian product" $
      forAll tinyList $ \xs ->
      forAll tinyList $ \ys ->
        toList (lmul (fromList xs) (fromList ys))
          === [(x, y) | x <- xs, y <- ys]

    prop "|lmul xs ys| == |xs| * |ys|" $
      forAll tinyList $ \xs ->
      forAll tinyList $ \ys ->
        Prelude.length (toList (lmul (fromList xs) (fromList ys)))
          === Prelude.length xs * Prelude.length ys

    prop "left absorbing (empty)" $
      forAll tinyList $ \xs ->
        toList (lmul (empty :: List Int) (fromList xs)) === []

    prop "right absorbing (empty)" $
      forAll tinyList $ \xs ->
        toList (lmul (fromList xs) (empty :: List Int)) === []
