import Mathlib

/-!
# Bézout's identity — statement B (Gauss, blind formalizer B)

Source (Wikipedia, "Bézout's identity", lead; retrieved 2026-11-26), quoted exactly:

> Let a and b be integers with greatest common divisor d. Then there exist integers x and y
> such that ax + by = d. Moreover, the integers of the form az + bt are exactly the multiples
> of d.

Mapping, one line per part of the quote:

* "Let a and b be integers"                  ↦ `∀ a b : ℤ`
* "with greatest common divisor d"           ↦ `∀ d : ℤ`, with the elementary characterisation
    `0 ≤ d`, `d ∣ a`, `d ∣ b`, and `∀ c : ℤ, c ∣ a → c ∣ b → c ∣ d`
    (d is the non-negative common divisor that every common divisor divides; this pins d down
    uniquely, gives gcd(0,0) = 0 as the issue requires, and agrees with "largest common divisor"
    whenever (a, b) ≠ (0, 0). The sanity section proves these hypotheses say exactly
    `d = Int.gcd a b`.)
* "there exist integers x and y"             ↦ `∃ x y : ℤ`
* "such that ax + by = d"                    ↦ `a * x + b * y = d`
* "Moreover, the integers of the form az + bt" ↦ `n` with `∃ z t : ℤ, a * z + b * t = n`
* "are exactly the multiples of d"           ↦ `↔ d ∣ n`, for every `n : ℤ`
-/

namespace TuriMath.BezoutIdentity.B

/-- `d` is the greatest common divisor of `a` and `b`, stated elementarily: a non-negative
common divisor that every common divisor divides. -/
def IsGcd (a b d : ℤ) : Prop :=
  0 ≤ d ∧ d ∣ a ∧ d ∣ b ∧ ∀ c : ℤ, c ∣ a → c ∣ b → c ∣ d

/-- Bézout's identity, both sentences of the source. -/
def Statement : Prop :=
  ∀ a b d : ℤ, IsGcd a b d →
    (∃ x y : ℤ, a * x + b * y = d) ∧
    (∀ n : ℤ, (∃ z t : ℤ, a * z + b * t = n) ↔ d ∣ n)

/-! ## Sanity section -/

/-- The hypotheses can all hold at once, for every `a b`: take `d = Int.gcd a b`. -/
example (a b : ℤ) : IsGcd a b (Int.gcd a b) :=
  ⟨Int.natCast_nonneg _, Int.gcd_dvd_left a b, Int.gcd_dvd_right a b,
    fun _ ha hb => Int.dvd_coe_gcd ha hb⟩

/-- The hypotheses determine `d`: it can only be `Int.gcd a b` (so the statement is not
vacuous and not about some other number). -/
example (a b d : ℤ) (h : IsGcd a b d) : d = Int.gcd a b := by
  obtain ⟨h0, ha, hb, hmax⟩ := h
  have h1 : d ∣ (Int.gcd a b : ℤ) := Int.dvd_coe_gcd ha hb
  have h2 : (Int.gcd a b : ℤ) ∣ d := hmax _ (Int.gcd_dvd_left a b) (Int.gcd_dvd_right a b)
  exact Int.dvd_antisymm h0 (Int.natCast_nonneg _) h1 h2

/-! ## Concrete checks -/

/-- a = 12, b = 18: gcd is 6, and 12·(−1) + 18·1 = 6. -/
example : Int.gcd 12 18 = 6 := by decide
example : IsGcd 12 18 6 :=
  ⟨by norm_num, by norm_num, by norm_num, fun _ ha hb => by
    have h := Int.dvd_coe_gcd ha hb
    rwa [show Int.gcd 12 18 = 6 by decide] at h⟩
example : ∃ x y : ℤ, 12 * x + 18 * y = 6 := ⟨-1, 1, by norm_num⟩
/-- 24 = 12·2 + 18·0 is of the form az + bt, and 6 ∣ 24; 9 is not a multiple of 6. -/
example : ∃ z t : ℤ, 12 * z + 18 * t = 24 := ⟨2, 0, by norm_num⟩
example : ¬ (6 : ℤ) ∣ 9 := by decide
/-- 3 is a common divisor of 12 and 18 but not *the* gcd: 6 ∣ 3 fails. -/
example : ¬ IsGcd 12 18 3 := fun h => absurd (h.2.2.2 6 (by norm_num) (by norm_num)) (by decide)

/-- a = −4, b = 6 (a negative input): gcd is 2, and (−4)·1 + 6·1 = 2. -/
example : Int.gcd (-4) 6 = 2 := by decide
example : ∃ x y : ℤ, (-4) * x + 6 * y = 2 := ⟨1, 1, by norm_num⟩

/-- a = b = 0: gcd(0,0) = 0, the only number of the form 0·z + 0·t is 0, the only multiple of 0. -/
example : IsGcd 0 0 0 := ⟨le_rfl, dvd_rfl, dvd_rfl, fun _ ha _ => ha⟩
example : ∃ x y : ℤ, (0 : ℤ) * x + 0 * y = 0 := ⟨0, 0, by norm_num⟩

/-- a = 7, b = 0: gcd is 7, and 7·1 + 0·0 = 7. -/
example : IsGcd 7 0 7 := ⟨by norm_num, dvd_rfl, dvd_zero 7, fun _ ha _ => ha⟩

end TuriMath.BezoutIdentity.B
