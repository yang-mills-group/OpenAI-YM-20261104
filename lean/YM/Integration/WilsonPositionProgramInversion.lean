import YM.Integration.WilsonPositionProgramCommonWindow
import YM.Integration.WilsonAdmissionScale
import YM.RG16.Provider.Slower

/-! Choose the common finite inversion top on the actual sequence, before the physical cutoffs. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramInversion
open Filter Lattice RG PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open WilsonPositionProgramCommonWindow
open scoped BigOperators Topology
variable {G : Gauge} (C : Run G) (simple : G.Simple) (D : XSpace.Run) {a : Axis} {ε : ℝ}
local notation "A" => C.family.path.levels
local notation "Λ" => RG16.Lambda A
local notation "β" => C.family.path.levels.clock.hatBeta

include simple in
private theorem allowance : ∀ᶠ m in atTop, (Λ m)^((3:ℝ)/2) ≤ β m := by
  let x := WilsonAdmissionScale.logarithm A
  have hx : Tendsto x atTop atTop := WilsonAdmissionScale.logarithm_tendsto A simple
  have small := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hx
  have bound : ∀ᶠ m in atTop, (x m)^2*Real.exp (-(x m)) < 1/4 :=
    small.eventually_lt_const (by norm_num)
  filter_upwards [hx.eventually_ge_atTop 2,bound] with m large low
  have pos : 0 < β m := zero_lt_one.trans (C.family.path.levels.fits.delayed m)
  change x m ^ 2 * Real.exp (-Real.log (β m)) < _ at low
  rw [Real.exp_neg,Real.exp_log pos,←div_eq_mul_inv,div_lt_iff₀ pos] at low
  have big : 1 ≤ 2+x m := by linarith
  calc (Λ m)^((3:ℝ)/2) ≤ (2+x m)^((2:ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le big (by norm_num)
    _ = (2+x m)^2 := Real.rpow_natCast ..
    _ ≤ β m := by nlinarith [sq_nonneg (x m-2),mul_nonneg (by linarith : 0 ≤ x m-2) (by linarith : 0 ≤ x m+2)]

theorem logged (m : ℕ) (w : ℕ → ℕ) (paid : ∀ j, (C.family.S.block (m+j)).val = D.ratio^w j)
    (j : ℕ) : C.family.S.scale (m+j) - C.family.S.scale m = (elapsed w j:ℝ)*Real.log D.ratio := by
  induction j with
  | zero => simp [elapsed]
  | succ j ih =>
    rw [←Nat.add_assoc,C.family.S.scale_succ,paid,Nat.cast_pow,Real.log_pow]
    rw [show elapsed w (j+1)=elapsed w j+w j from Finset.sum_range_succ ..,Nat.cast_add,add_mul]
    linarith

/-- The independent fine-date parameter and the admissible native period are chosen from the
actual variable blocks. Its inverse spacing has the manuscript's three-halves logarithmic order. -/
theorem chosen (purchase : WilsonPositionProgramElection.course simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (hr : D.ratio = 3^d)
    (pace : ∀ m, ((C.family.S.block m).val:ℝ) ≤ Real.log (Λ m)) :
    ∀ᶠ m in atTop, ∃ (w : ℕ → ℕ) (j : ℕ), 0 < j ∧
      (∀ k, (C.family.S.block (m+k)).val = D.ratio^w k) ∧
      C.family.S.a (m+j) / C.family.S.a m = (D.step (elapsed w j)).spacing ∧
      Λ m ^ ((3:ℝ)/2) ≤ (elapsed w j : ℝ)*Real.log D.ratio ∧
      (elapsed w j : ℝ)*Real.log D.ratio ≤ Λ m ^ ((3:ℝ)/2) + 2*Λ m := by
  let x := WilsonAdmissionScale.logarithm A
  have hx : Tendsto x atTop atTop := WilsonAdmissionScale.logarithm_tendsto A simple
  have slope := Gauge.slopeConstant_pos simple
  filter_upwards [dates C D purchase hd hr,allowance C simple,
    hx.eventually_ge_atTop (Real.log (1+G.slopeConstant))] with m eligible capped large
  obtain ⟨w,paid⟩ := eligible
  let need := (Λ m)^((3:ℝ)/2)
  have pos : 0 < Λ m := by
    exact add_pos (by norm_num) (WilsonAdmissionScale.logarithm_pos A m)
  have existsDate : ∃ j : ℕ, need ≤ C.family.S.scale (m+j) - C.family.S.scale m := by
    have go : Tendsto (fun j : ℕ => m+j) atTop atTop :=
      tendsto_atTop_mono (fun j => Nat.le_add_left j m) tendsto_id
    obtain ⟨j,hj⟩ := ((C.family.S.divergent.comp go).eventually_ge_atTop (C.family.S.scale m + need)).exists
    exact ⟨j,by change _ ≤ C.family.S.scale (m+j) at hj; linarith⟩
  let j := Nat.find existsDate
  have reaches : need ≤ C.family.S.scale (m+j)-C.family.S.scale m := Nat.find_spec existsDate
  have positive : 0 < j := by
    by_contra! hn
    rw [Nat.le_zero.mp hn,Nat.add_zero,sub_self] at reaches
    exact (Real.rpow_pos_of_pos pos _).not_ge reaches
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  have before : C.family.S.scale (m+k)-C.family.S.scale m < need :=
    lt_of_not_ge (Nat.find_min existsDate (show k < j by omega))
  have price : β (m+k) ≤ (1+G.slopeConstant) * β m := by
    have shift : β (m+k)-β m = G.slopeConstant * (C.family.S.scale (m+k)-C.family.S.scale m) := by
      unfold RG.Calendar.hatBeta
      ring
    have xpay := mul_le_mul_of_nonneg_left (before.le.trans capped) slope.le
    nlinarith
  have bpos : 0 < β m := zero_lt_one.trans (C.family.path.levels.fits.delayed m)
  have logpay := Real.log_le_log (zero_lt_one.trans (C.family.path.levels.fits.delayed (m+k))) price
  rw [Real.log_mul (by linarith : (1+G.slopeConstant:ℝ) ≠ 0) bpos.ne'] at logpay
  have lap : Real.log ((C.family.S.block (m+k)).val:ℝ) ≤ 2 * Λ m := by
    have v₁ := Real.log_le_sub_one_of_pos (by exact_mod_cast (C.family.S.block (m+k)).property : 0 < ((C.family.S.block (m+k)).val:ℝ))
    have v₂ := Real.log_le_sub_one_of_pos (add_pos (by norm_num : (0:ℝ)<2) (WilsonAdmissionScale.logarithm_pos A (m+k)))
    have budget := pace (m+k)
    change Real.log (1+G.slopeConstant) ≤ Real.log (β m) at large
    change Real.log (2+Real.log (β (m+k))) ≤ 2+Real.log (β (m+k))-1 at v₂
    change _ ≤ Real.log (2+Real.log (β (m+k))) at budget
    change _ ≤ 2*(2+Real.log (β m))
    linarith
  refine ⟨w,j,positive,paid,fine_spacing C D m w paid j,?_,?_⟩
  · exact (logged C D m w paid j) ▸ reaches
  · rw [←logged C D m w paid j,hk]
    change C.family.S.scale ((m+k)+1)-C.family.S.scale m ≤ need + 2*Λ m
    rw [C.family.S.scale_succ]
    linarith

end YM.Integration.WilsonPositionProgramInversion
end
