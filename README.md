# system-f-numerical

Church-encoded natural numbers, finite lists, and the full
**hyperoperation hierarchy** — addition, multiplication,
exponentiation, tetration, pentation — in roughly forty lines of pure
System F.

All computation is driven by polymorphic instantiation. There is no
recursion over a data constructor, no `Data.Nat` GADT, no pattern
matching on representatives of the encoding.

## The idea

A natural number is an iteration operator. In System F:

```haskell
type Nat = forall x. (x -> x) -> (x -> x)

zero :: Nat
zero _ = id

suc :: Nat -> Nat
suc n f = f . n f
```

Addition composes iteration; multiplication nests it:

```haskell
add n m f = n f . m f     -- f applied n + m times
mul n m f = n (m f)       -- f applied n * m times
```

Each successive hyperoperation is obtained by **iterating the previous
one from `1`**:

```
b^e        =  iterate (mul b) e times from 1
b ↑↑ e     =  iterate (exp b) e times from 1
b ↑↑↑ e    =  iterate (tet b) e times from 1
```

That is itself a Church-numeral operation, so we can name it:

```haskell
hypSuc :: BinOp Nat -> BinOp Nat
hypSuc h b e = e @Nat (h b) (suc zero)

exp  = hypSuc mul
tet  = hypSuc exp
pent = hypSuc tet
```

The type application `e @Nat` instantiates the universally-quantified
`x` in `Nat` at the polymorphic type `Nat` itself. That is
**impredicative polymorphism**, and it is what makes the one-liner
`hypSuc` type-check.

## Example

```
ghci> toInteger (exp  (fromInteger 2) (fromInteger 10))
1024
ghci> toInteger (exp  (fromInteger 2) (fromInteger 16))
65536
ghci> toInteger (tet  (fromInteger 2) (fromInteger 4))
65536              -- = 2^(2^(2^2))
ghci> toInteger (pent (fromInteger 2) (fromInteger 3))
65536              -- = 2 ↑↑ (2 ↑↑ 2) = 2 ↑↑ 4
```

## Lists as a companion

The same trick gives a Church encoding of finite lists — it is the
natural-number encoding with an extra element argument at each fold
step:

```haskell
type List a = forall x. (a -> x -> x) -> (x -> x)
```

Operations parallel the numeric ones exactly:

| Natural | Definition  | List     | Definition                               |
| ------- | ----------- | -------- | ---------------------------------------- |
| `add`   | `n f . m f` | `append` | `l1 f . l2 f`                            |
| `mul`   | `n (m f)`   | `lmul`   | `l1 (\a -> l2 (\b x -> f (a,b) x))`      |

`lmul` is the Cartesian product, enumerated in lexicographic order.

## Building

```
cabal build
cabal test
```

The test suite is `hspec` + `QuickCheck`: 124 cases covering

- round-trip properties for `Nat` ↔ `Integer` and `List` ↔ `[]`,
- arithmetic laws (associativity, commutativity, distributivity,
  identity and zero elements),
- the cross-operation identities `b^(x+y) = b^x · b^y` and
  `pent b (e+1) = tet b (pent b e)`,
- small-value vetting of tetration and pentation against independently
  computed power-tower values,
- the list monoid laws for `append` and the Cartesian-product laws
  for `lmul`.

## Requirements

- GHC 9.6+ — the module uses `ImpredicativeTypes`, `RankNTypes`, and
  `TypeApplications`.

## Caveats

`toInteger` and `fromInteger` in the library are the direct System-F
definitions and are *not* stack-safe for large `n`. Stack-safe
counterparts (`toIntegerStrict`, `fromIntegerStrict`) live in the test
suite and can be copy-pasted if you want to evaluate large numerals
interactively.

## References

- Alonzo Church, *The Calculi of Lambda-Conversion*, 1941.
- Jean-Yves Girard, *Interprétation fonctionnelle et élimination des
  coupures de l'arithmétique d'ordre supérieur*, 1972.
- John C. Reynolds, *Towards a theory of type structure*, 1974.
- Donald E. Knuth, "Mathematics and Computer Science: Coping with
  Finiteness," *Science* 194 (1976), pp. 1235–1242 — the up-arrow
  notation.

## License

BSD-3-Clause. See [LICENSE](LICENSE).
