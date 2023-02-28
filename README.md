This is grhkm's [Lean 4](https://github.com/leanprover/lean4) experiment repo! I started learning Lean 4 since around 24 Feb 2023. You will find all kinds of crazy ideas here. Recently I am working on proving theorems about monads, such as proving the following:

```lean
import Mathlib.Data.Nat.Basic

def ff (n : ℕ) : ℕ := Id.run do
  let mut r := 0
  for _ in [: n] do
    r ← r + 1
  return r

theorem ff' : ff n = n := sorry
```

Here are some of the ideas that I have explored in the past two months, mostly on Lean 3 (see my [Lean 3 repo](https://github.com/grhkm21/lean)):

-   [Bernoulli polynomials](https://github.com/leanprover-community/mathlib/pull/18313)
-   Euclid-Euler Theorem, that every perfect number is in the form of $2^(p - 1)(2^p - 1)$
-   Bounding π(x), the prime-counting function
-   Conway's look-and-say sequence and cosmological sequence
-   Sylvester-Gallai Theorem, that there exists an ordinary line
-   Defining the p.m.f. of a Poisson distribution

If you have any feedback / suggestions for me, please DM me on Discord at grhkm#4429!
