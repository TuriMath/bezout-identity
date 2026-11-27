import Mathlib

/-!
# Bézout's identity — statement A (Noether)

Source (Wikipedia, "Bézout's identity", lead; quoted in TuriMath/bezout-identity#1):
> Let a and b be integers with greatest common divisor d. Then there exist integers x and y
> such that ax + by = d. Moreover, the integers of the form az + bt are exactly the multiples of d.

Choices:
* ℤ throughout, because the source says "integers" (no sign or non-zero restriction, so
  `a = b = 0` is included).
* `d` is `Int.gcd a b` cast to ℤ: Mathlib's greatest common divisor on ℤ, the non-negative one,
  so `gcd 0 0 = 0` (issue notes). `d` is bound explicitly with the hypothesis `d = gcd a b`
  to mirror "with greatest common divisor d".
* "the integers of the form az + bt are exactly the multiples of d" is a set equality in ℤ.
-/

namespace TuriMath.BezoutIdentity.A

/-- Bézout's identity.

* "Let a and b be integers"                        ↦ `∀ a b : ℤ`
* "with greatest common divisor d"                 ↦ `∀ d : ℤ, d = (Int.gcd a b : ℤ) → …`
* "there exist integers x and y"                   ↦ `∃ x y : ℤ`
* "such that ax + by = d"                          ↦ `a * x + b * y = d`
* "Moreover"                                       ↦ `∧`
* "the integers of the form az + bt"               ↦ `{n : ℤ | ∃ z t : ℤ, a * z + b * t = n}`
* "are exactly"                                    ↦ `=` (equality of sets)
* "the multiples of d"                             ↦ `{n : ℤ | d ∣ n}`
-/
def Statement : Prop :=
  ∀ a b : ℤ, ∀ d : ℤ, d = (Int.gcd a b : ℤ) →
    (∃ x y : ℤ, a * x + b * y = d) ∧
    {n : ℤ | ∃ z t : ℤ, a * z + b * t = n} = {n : ℤ | d ∣ n}

/-! ## Sanity section
The only hypothesis is `d = gcd a b`. It can hold, for any `a b`; two instances below,
including the degenerate `a = b = 0`. -/

example : ∃ a b d : ℤ, d = (Int.gcd a b : ℤ) := ⟨12, 18, 6, by decide⟩

example : ∃ a b d : ℤ, d = (Int.gcd a b : ℤ) := ⟨0, 0, 0, by decide⟩

example (a b : ℤ) : ∃ d : ℤ, d = (Int.gcd a b : ℤ) := ⟨_, rfl⟩

end TuriMath.BezoutIdentity.A
