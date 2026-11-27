import Theorems.BezoutIdentity.A

namespace TuriMath.BezoutIdentity

/-- Euclid's algorithm on the second argument, by strong induction on `|b|`. -/
theorem exists_comb : ∀ n : ℕ, ∀ a b : ℤ, b.natAbs = n →
    ∃ x y : ℤ, a * x + b * y = (Int.gcd a b : ℤ) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b hn
    by_cases hb : b = 0
    · subst hb
      refine ⟨Int.sign a, 0, ?_⟩
      simp [Int.mul_sign_self, Int.natCast_natAbs]
    · have hlt : (a % b).natAbs < n := by
        have h1 := Int.emod_nonneg a hb
        have h2 := Int.emod_lt a hb
        omega
      obtain ⟨x, y, h⟩ := ih _ hlt b (a % b) rfl
      have hg : Int.gcd b (a % b) = Int.gcd a b := by
        rw [Int.gcd_comm, Int.gcd_emod]
      rw [hg] at h
      refine ⟨y, x - (a / b) * y, ?_⟩
      rw [← h, Int.emod_def]
      ring

theorem main : A.Statement := by
  intro a b d hd
  subst hd
  obtain ⟨x, y, hxy⟩ := exists_comb _ a b rfl
  refine ⟨⟨x, y, hxy⟩, Set.ext fun n => ?_⟩
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, t, rfl⟩
    exact dvd_add (Dvd.dvd.mul_right (Int.gcd_dvd_left a b) _)
      (Dvd.dvd.mul_right (Int.gcd_dvd_right a b) _)
  · rintro ⟨k, rfl⟩
    exact ⟨x * k, y * k, by rw [← mul_assoc, ← mul_assoc, ← add_mul, hxy]⟩

end TuriMath.BezoutIdentity
