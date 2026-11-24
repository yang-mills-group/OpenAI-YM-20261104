import YM.Integration.WilsonEmittedRootSalary
import YM.QuadraticLocal.Fk.Offer

/-! The original single funded roster pays its entire joint derivative
on its literal marked root. An address can select the full mode or the
long-word part without changing the rooted or finite-period purchase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedLocatedCensus
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Push.AbsoluteSums Comparison.Density AnalyticBridge.SectorAffine.Offset
open WilsonEmittedWordJointFare WilsonEmittedRootSalary
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (w : V → ℝ) (grades : V → ℕ) {σ b a g K θ : ℝ} {p pieces depth : ℕ}
variable (old : Armada M w grades σ b p pieces depth) (B : BudgetPoint)
variable (scope : Invoice.Supports B K a g σ θ)

def receipt (G : Gauge) (B : BudgetPoint) (j s pieces m : ℕ) (b a θ : ℝ) :=
  Footprint.payment 1 (B.B+2) (j*s) θ (fee G j s) b a (Invoice.tax s pieces) * Real.exp (-θ)^m

include scope old in
theorem paid (j m : ℕ) (s : Γ.Mode) (v : V) (hv : v ∈ s.val) (x : X)
    (chosen : ι → Prop) (cover : ∀ i, chosen i → s=(M i).mode ∧ m≤(M i).length) :
    SumBudget (WilsonEmittedRootCensus.price M (fun i => (M i).paint x) chosen j)
      ((Poly.toll w s)⁻¹ * receipt G B j (p+depth+1) pieces m b a θ) := by
  have all := tail M w grades old B scope x j m (P.origin v)
  have price := Poly.worth old.positive s
  apply budget_mono (budget_scale (inv_nonneg.mpr price.le) all)
  · intro i
    by_cases h : chosen i
    · simp only [WilsonEmittedRootCensus.price,if_pos h]
      exact mul_nonneg (norm_nonneg _) (tested (M i) (M i).lamp.power j (0:Chart G n) (by simp)).nonneg
    · simp [WilsonEmittedRootCensus.price,h]
  · intro i
    by_cases h : chosen i
    · obtain ⟨mode,hl⟩ := cover i h
      have home : P.origin v ∈ (M i).ground B := (M i).heard _ v (mode ▸ hv) (P.born v)
      simp only [WilsonEmittedRootCensus.price,if_pos h,if_pos hl,if_pos home,rent,←mode]
      rw [←mul_assoc,←mul_assoc,inv_mul_cancel₀ price.ne',one_mul]
      apply le_mul_of_one_le_right (mul_nonneg (norm_nonneg _)
        (tested (M i) (M i).lamp.power j (0:Chart G n) (by simp)).nonneg)
      exact Real.one_le_exp (mul_nonneg scope.2.2.2.2.2.1 (Nat.cast_nonneg _))
    · simp only [WilsonEmittedRootCensus.price,if_neg h]
      exact mul_nonneg (inv_nonneg.mpr price.le) (all.1 i)

include scope old in
theorem original (j m : ℕ) (s : Γ.Mode) (v : V) (hv : v ∈ s.val) (x : X)
    (chosen : ι → Prop) (cover : ∀ i, chosen i → s=(M i).mode ∧ m≤(M i).length)
    (z : Chart G n) (hz : ‖z‖ ≤ 1) :
    Through j (WilsonEmittedRootCensus.field M (fun i => (M i).paint x) chosen) z
      ((Poly.toll w s)⁻¹ * receipt G B j (p+depth+1) pieces m b a θ) := by
  have hb : 0 < (B.B:ℝ) := Nat.cast_pos.mpr B.B_pos
  have hs := scope.2.2.2.2.2
  have width : 0 < σ := (add_pos_of_nonneg_of_pos
    (mul_nonneg hs.1 (inv_nonneg.mpr hb.le)) (mul_pos (by norm_num) hs.2.1)).trans_le hs.2.2
  have staff := Air.license M (fun i => (M i).paint x) grades w old width (fun i => old.honor i x)
  exact WilsonEmittedRootCensus.tested M _ chosen grades staff j
    (paid M w grades old B scope j m s v hv x chosen cover) z hz

end YM.Integration.WilsonEmittedLocatedCensus
