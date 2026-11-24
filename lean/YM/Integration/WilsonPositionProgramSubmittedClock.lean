import YM.Integration.WilsonPositionProgramSubmittedRate
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramSubmittedClock
open Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl RegulatorIR RegulatorIR.Ledger RegulatorIR.Uniform
open scoped ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j:X→ℕ) (w : X→ℕ→ℕ) (i : X→ℕ) (H : ℝ)
local notation "L" => WilsonPositionProgramInfraredMeter.wallet C D m j w i H

theorem paid : (Poly L fun x=> ‖((D.step (i x)).spacing)⁻¹‖ₑ) ∧
    (Poly L fun x=> ‖Real.log (D.step (i x)).spacing‖ₑ) := by
  have inv (x:X) : ((D.step (i x)).spacing)⁻¹  ≤  WilsonPositionProgramInfraredMeter.amount C D m j w i H x := by
    have nonneg := (RG16.Literal.lambda_pos C.family (m x+j x)).le
    have ε := (D.step (i x)).positive
    have h : (1:ℝ) ≤ max 0 H+1 := by linarith [le_max_left 0 H]
    have k := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr ε.le)
    dsimp only [WilsonPositionProgramInfraredMeter.amount]
    rw [div_eq_mul_inv]; linarith [abs_nonneg (Real.log
      ((WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val:ℝ))]
  constructor
  · apply (Poly.roof L).mono
    intro x
    dsimp only
    rw [←ofReal_norm,Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (D.step _).positive)]
    exact ENNReal.ofReal_le_ofReal (inv x)
  apply (Poly.roof L).mono
  intro x
  dsimp only
  have pow1 : 1 ≤ (D.ratio^(i x):ℕ) := one_le_pow₀ ((by decide : 1 ≤ 3).trans D.large)
  have denom : 1 ≤ ((D.den (i x)):ℝ) := by exact_mod_cast pow1
  have pos := lt_of_lt_of_le zero_lt_one denom
  rw [←ofReal_norm,Real.norm_eq_abs]
  apply ENNReal.ofReal_le_ofReal
  apply le_trans _ (inv x)
  change |Real.log (((D.den (i x)):ℝ)⁻¹)|  ≤  (((D.den (i x)):ℝ)⁻¹)⁻¹
  rw [Real.log_inv, abs_neg, abs_of_nonneg (Real.log_nonneg denom), inv_inv]
  linarith [Real.log_le_sub_one_of_pos pos]

end YM.Integration.WilsonPositionProgramSubmittedClock
