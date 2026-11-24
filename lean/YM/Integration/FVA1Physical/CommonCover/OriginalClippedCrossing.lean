import YM.Integration.FVA1Physical.CommonCover.ClippedSpectator
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionRelativeInvoice

/-! Truncate the invoice for the original restored pair before testing it.
All four crossing rows and both raw singleton rows refer to the same Gallery,
gas, field, and first clear annulus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Crossing
open Finset Lattice RG Wilson Marker QuadraticLocal Push.AbsoluteSums.Animals
open Extra.Trajectories MeasureTheory Exchange.RoseCut
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V T I : Type} [Fintype V] [DecidableEq V]
  {C : Census V} {o : V → Site n} {P : Rep G n} (A : Gallery T I o P C)

def rawSingleton (t : T) (w : V → ℝ) (d : V) (U : Config G n) : ℝ :=
  ‖(w d : ℂ) * (A.gas t U).part (C.fire d)‖

omit [Fintype V] in
theorem original_invoice (t : T) (a b : V) (s : C.Mode) (w : V → ℝ)
    (D m : ℕ) (M : ℝ) (U : Config G n) (live : 0 < P.eval U) :
    relativeInvoice A t a b s w D m M U =
      invoice (P.activities.gas P.p U) (crossingWallet A t a b s w D m U) M
        (rawSingleton A t w a U) (rawSingleton A t w b U) := by
  have gas : 0 < P.activities.gas P.p U := pos_of_mul_pos_right live (Real.exp_nonneg _)
  simp only [relativeInvoice, invoice, rawSingleton, ← mul_div_assoc, norm_div,
    Complex.norm_real, Real.norm_of_nonneg gas.le]

omit [Fintype V] in
theorem original_wallet_nonneg (t : T) (a b : V) (s : C.Mode) (w : V → ℝ)
    (D m : ℕ) (U : Config G n) : 0 ≤ crossingWallet A t a b s w D m U := by
  apply Finset.sum_nonneg
  intro j _
  apply Set.indicator_nonneg (fun _ _ => ?_)
  exact (norm_nonneg _).trans ((le_max_left ..).trans (le_max_left ..))

/-- On the selected physical outside-crowd event, only a single inverse
vacuum occurs in the square of the remaining error envelope. -/
theorem original_restored_clipped (t : T) (a b : V) (s : C.Mode) (pair : s.val = {a,b})
    (w : V → ℝ) (wp : ∀ v, 0 < w v) (e κ : ℝ) (paid : A.K.Paid w P.p.B e κ)
    (en : 0 ≤ e) (small : κ ≤ 1) (m D : ℕ)
    (far : m*(2*width P.p D) < separation (o a) (o b)) (U : Config G n)
    (live : 0 < P.eval U)
    (out : U ∉ crowd P.p.threshold (neighbors (m*(2*width P.p D)) (o a)) m)
    (δ : ℂ) (M : ℝ) (cap : ‖((w a : ℂ)*(w b : ℂ))*δ‖ ≤ M)
    (unit : P.activities.gas P.p U ≤ 1)
    (rawA : rawSingleton A t w a U ≤ κ) (rawB : rawSingleton A t w b U ≤ κ) :
    let τ : ℂ := (w a : ℂ)*(w b : ℂ)
    let W := crossingWallet A t a b s w D m U
    ‖τ*δ‖ ≤ ‖τ*(δ-filedRow A t s U)‖ +
      Real.sqrt ((M^5*(2*W*(M+(1+κ)^2)))^((3:ℝ)⁻¹)/(P.activities.gas P.p U)) := by
  intro τ W
  have gas : 0 < P.activities.gas P.p U := pos_of_mul_pos_right live (Real.exp_nonneg _)
  have c := clipped_square gas unit (original_wallet_nonneg A t a b s w D m U)
    ((norm_nonneg _).trans cap) (norm_nonneg _) (norm_nonneg _) rawA rawB
  have basic := relative_field A t a b s pair w wp e κ paid en small m D far U live out δ M cap
  rw [original_invoice A t a b s w D m M U live] at basic
  apply (clip_error cap (norm_nonneg _) basic).trans
  apply add_le_add le_rfl
  exact (le_abs_self _).trans ((Real.sqrt_sq_eq_abs _).symm.le.trans
    (Real.sqrt_le_sqrt ((le_div_iff₀ gas).2 c)))

end YM.Integration.FVA1Physical.Crossing
