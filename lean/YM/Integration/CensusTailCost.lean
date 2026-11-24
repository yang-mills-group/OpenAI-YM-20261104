import YM.Integration.UnmarkedContractionAdmission
import YM.Integration.WilsonLimitConstruction.FundedSurplusPrice

/-! The signed discarded cluster's actual canonical extraction fee on the
coarse requested norm at every later cutoff and period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.CensusTailCost

open Filter Lattice Wilson RG Marker
open PhysicalNext.Repeat.Legato IterationFour
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Pert.Asymptotics MatchingLedger.Compass.Income
open scoped Topology

variable {G : Gauge} {V : Type} {J : Request V}

/-- A truncation at the requested order pays the full actual extraction
factor with any positive coefficient at the coarse requested exponent. -/
theorem estimate (R : Run G) (hG : G.Simple) (A : NumericSchedule R.family J)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ m : ℕ in atTop, ∀ N p : ℕ, m < N →
      ActualNextInheritedPrice.extractionFactor R A m *
        (2*regulatorRun R.family N p (m+1))^(J.order+1) ≤
          ε*regulatorRun R.family N p m^((J.order:ℝ)+1-J.eta) := by
  let C := ActualCanonicalPayloadPrice.coefficient G (A.outputNorm 0)
  let d := ActualCanonicalPayloadPrice.degree (A.outputNorm 0)
  let t := (2:ℝ)^(J.order+1)
  let s := (J.order:ℝ)+1-J.eta
  have hC : 0 < C := ActualCanonicalPayloadPrice.coefficient_positive G _
  have ht : 0 < t := pow_pos (by norm_num) _
  have hsmall := WilsonLimitConstruction.FundedSurplusPrice.cost_small R hG A
    (2*C*t) (by positivity) d J.eta ε J.eta_pos hε
  have hadj := UnmarkedContractionAdmission.adjacent R hG s (T := 2) (by norm_num)
  filter_upwards [hsmall, hadj] with m hm ha
  intro N p hN
  let gf := regulatorRun R.family N p (m+1)
  let gc := regulatorRun R.family N p m
  let B := ActualNextInheritedPrice.extractionFactor R A m
  have hf : 0 < gf := Weather.runs_pos R.family R.makes (Nat.succ_le_of_lt hN) p
  have hg : 0 < gc := Weather.runs_pos R.family R.makes hN.le p
  have hB : B ≤ C*A.admittedCost m^d := ActualCanonicalPayloadPrice.scheduled_factor R A m
  have hs : gf^(J.order+1) = gf^J.eta * gf^s := by
    rw [← Real.rpow_natCast, Nat.cast_add, Nat.cast_one,
      show (J.order:ℝ)+1 = J.eta+s by dsimp only [s]; ring, Real.rpow_add hf]
  have hA := A.admitted_cost_nonnegative m
  change B*(2*gf)^(J.order+1) ≤ ε*gc^s
  calc
    _ ≤ (C*A.admittedCost m^d)*(2*gf)^(J.order+1) :=
        mul_le_mul_of_nonneg_right hB (pow_nonneg (by positivity) _)
    _ = (C*t*A.admittedCost m^d*gf^J.eta)*gf^s := by
        rw [mul_pow, hs]; dsimp only [t]; ring
    _ ≤ (C*t*A.admittedCost m^d*gf^J.eta)*(2*gc^s) :=
        mul_le_mul_of_nonneg_left (ha N p hN) (by positivity)
    _ = ((2*C*t)*A.admittedCost m^d*gf^J.eta)*gc^s := by ring
    _ ≤ ε*gc^s := mul_le_mul_of_nonneg_right (hm N p hN) (Real.rpow_nonneg hg.le _)

end YM.Integration.CensusTailCost
end
