import Theorems.BezoutIdentity.A
import Theorems.BezoutIdentity.B

namespace TuriMath.BezoutIdentity

/-- B's elementary `IsGcd` is the same as A's `d = Int.gcd a b`. -/
theorem isGcd_iff (a b d : ℤ) : B.IsGcd a b d ↔ d = (Int.gcd a b : ℤ) := by
  constructor
  · rintro ⟨h0, ha, hb, hmax⟩
    exact Int.dvd_antisymm h0 (Int.natCast_nonneg _) (Int.dvd_coe_gcd ha hb)
      (hmax _ (Int.gcd_dvd_left a b) (Int.gcd_dvd_right a b))
  · rintro rfl
    exact ⟨Int.natCast_nonneg _, Int.gcd_dvd_left a b, Int.gcd_dvd_right a b,
      fun _ ha hb => Int.dvd_coe_gcd ha hb⟩

theorem equiv : A.Statement ↔ B.Statement := by
  constructor
  · intro h a b d hd
    obtain ⟨h1, h2⟩ := h a b d ((isGcd_iff a b d).1 hd)
    refine ⟨h1, fun n => ?_⟩
    have := Set.ext_iff.1 h2 n
    simpa using this
  · intro h a b d hd
    obtain ⟨h1, h2⟩ := h a b d ((isGcd_iff a b d).2 hd)
    refine ⟨h1, Set.ext fun n => ?_⟩
    simpa using h2 n

end TuriMath.BezoutIdentity
