import YM.Integration.NativeDiagonalClockRequest
import YM.Integration.FullQLocalStrongApplication

/-! Specialize the single diagonal request to already selected qlocal width
families.  The family is fixed before the shared construction, and each demand
has its own eventual first stage on that same Family.  This file does not
select Sheet-dependent widths or their pre-block floors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCountableWidthPayment
open Lattice RG RG.Supply Push.PriceCompiler
open PhysicalNext.Repeat.Legato.R2I FullQLocal

variable {G : Gauge}

def PaidWidths (W : ℕ → ProfileWidths) (A : Levels G) : Prop :=
  NativeDiagonalClockRequest.PaidRequests (fun n i => ((W n).width i)⁻¹) A

theorem eventuallyPaid (W : ℕ → ProfileWidths) :
    EventuallyPaid (PaidWidths (G := G) W) :=
  NativeDiagonalClockRequest.eventuallyPaid _

/-- Coefficient and degree stay one; only the eventual first index depends on
the fixed demand.  The Run/Family is never reselected as n changes. -/
def payment (W : ℕ → ProfileWidths) (C : Family G)
    (h : PaidWidths W C.path.levels) (n : ℕ) : WidthPayment C (W n) where
  coefficient := 1
  coefficient_nonnegative := zero_le_one
  degree := 1
  first := Classical.choose (h.2 n)
  scale_ge_one m _ := h.1 m
  reciprocal m hm := by
    have hb := Classical.choose_spec (h.2 n)
    have hi (i : ℕ) (hik : i ≤ C.path.levels.clock.J (m + 1)) :
        ((W n).width i)⁻¹ ≤
          1 + Real.log (Real.log (C.path.levels.clock.hatBeta m)) := by
      simpa only [abs_of_nonneg (inv_nonneg.mpr ((W n).positive i).le)]
        using hb m hm i hik
    rcases le_total ((W n).width (C.path.levels.clock.J (m + 1)))
      ((W n).width (C.path.levels.clock.J m)) with hle | hle
    · simpa only [one_mul, pow_one, ProfileWidths.pair, widthScale,
        min_eq_left hle] using hi (C.path.levels.clock.J (m + 1)) le_rfl
    · simpa only [one_mul, pow_one, ProfileWidths.pair, widthScale,
        min_eq_right hle] using
        hi (C.path.levels.clock.J m) (C.path.levels.fits.mono (Nat.le_succ m))

end YM.Integration.ActualCountableWidthPayment
end
