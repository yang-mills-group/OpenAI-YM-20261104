import YM.Integration.WilsonThermometerUnitFilingFourPoolShell
import YM.Integration.WilsonNormalizedReflectedForm
import YM.Integration.WilsonMatrixOriginalDeckCapacity
import YM.Integration.WilsonInvariantActionSpectatorPrices

/-! The small-scale factory and reflected chamber hear the original charged fields
at either spatial scale through a single relative-frame estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 260000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFourPoolRent
open Function Filter Set Table Spec Climb Maxwell Maxwell.Free RG05Readout
open Lattice Wilson RG Source Extraction OPE Trace.Pilot PhysMS Frame
open GapsContact GapsContact.Seams PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register MS MS.Land
open WilsonPositionHomogeneousFrame WilsonInvariantActionSpectatorPrices
open WilsonMatrixOriginalDeckCapacity
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
  (F : Final R.family f S) (J : ℝ→tower S) (Z : WilsonPrescription G)
  {H : (Bel R.family.book).Hierarchy}

include Z in
theorem primary (lead : Leading F J) (d : ℕ) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ r in trail, ∀ y : S.Field d,
      Ascent.cost F d r y ≤ B*capacity d J r y := by
  obtain ⟨B,nonneg,bill⟩ := WilsonNormalizedReflectedForm.uniform F J Z.store lead d (zero_le_one:0≤(1:ℝ))
  refine ⟨B,nonneg,?_⟩
  filter_upwards [bill] with r quote y
  let x := (J r d).symm y
  have hy : J r d x = y := LinearEquiv.apply_symm_apply _ _
  rw [←hy]
  change Ascent.cost F d r (J r d x) ≤ B*‖(J r d).symm (J r d x)‖
  rw [LinearEquiv.symm_apply_apply]
  by_cases zero : x=0
  · simp [zero,Ascent.cost_zero]
  have pos := norm_pos_iff.mpr zero
  have cn : (‖x‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr pos.ne'
  let a := (‖x‖:ℂ)⁻¹ • x
  have unit : ‖a‖≤1 := by
    simp only [a,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos,inv_mul_cancel₀ pos.ne',le_refl]
  have whole : (‖x‖:ℂ) • a=x := by simp [a,smul_smul,cn]
  have due : Ascent.cost F d r (J r d a) ≤ B := quote false a unit
  calc Ascent.cost F d r (J r d x) = ‖x‖*Ascent.cost F d r (J r d a) := by
         conv_lhs => rw [←whole,map_smul,Ascent.cost_hom,Complex.norm_real,Real.norm_eq_abs,abs_of_pos pos]
       _ ≤ B*‖x‖ := by rw [mul_comm B]; exact mul_le_mul_of_nonneg_left due pos.le

theorem converted (simple : G.Simple) (lead : Leading F J)
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, Frame.obedient F H (J r) d)
    (d : ℕ) (v : RG17.Free R.family d) {u a : ℝ→ℝ}
    (old : Tendsto u trail trail) (young : Tendsto (fun r=>a r*u r) trail trail)
    (within : ∀ᶠ r in trail, a r∈Set.Ioc (0:ℝ) 1) :
    ∃ B : ℝ, 0≤B ∧ ∀ η : ℝ, 0<η → ∀ᶠ r in trail,
      Ascent.cost F d (a r*u r) (homogeneous F J Z (u r) d v) ≤
        B*(a r)^(-(d:ℝ)-η) := by
  obtain ⟨B,bp,unit⟩ := primary F J Z lead d
  obtain ⟨K,kp,relative⟩ := WilsonMatrixOriginalDeckCapacity.original F d J lead
  have normed := (WilsonOriginalCompensatedAnchor.field F J Z lead paid simple d v).norm
  have lim : ∀ᶠ r in trail, ‖freeInput F J Z d r v‖ ≤ ‖v‖+1 :=
    normed.eventually (ge_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
  refine ⟨B*K*(‖v‖+1),by positivity,fun η hp=>?_⟩
  filter_upwards [young.eventually unit,old.eventually (relative η hp),within,old.eventually lim]
    with r price quote member normBound
  let field := homogeneous F J Z (u r) d v
  have identify : capacity d J (u r) field = ‖freeInput F J Z d (u r) v‖ := by
    change ‖(J (u r) d).symm (J (u r) d (freeInput F J Z d (u r) v))‖=_
    rw [LinearEquiv.symm_apply_apply]
  have step := (quote _ member field).1
  rw [identify] at step
  have fac : 0≤(a r)^(-(d:ℝ)-η) := Real.rpow_nonneg member.1.le _
  calc Ascent.cost F d (a r*u r) field ≤ B*capacity d J (a r*u r) field := price field
       _ ≤ B*(K*(a r)^(-(d:ℝ)-η)*(‖v‖+1)) :=
         mul_le_mul_of_nonneg_left (step.trans (mul_le_mul_of_nonneg_left normBound (by positivity))) bp
       _ = _ := by ring

end YM.Integration.WilsonThermometerUnitFilingFourPoolRent
