import YM.Integration.WilsonMacroscopicRichTwoDatePivot
import YM.Integration.WilsonNormalizedReflectedForm

/-! The true outer public field in the near-scale spectral tube. All physical
normalizations, including its lower components, are kept. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkFarCost
open Function Filter Set Metric Extraction Spec PhysMS Trace Trace.Pilot Climb
open GapsContact GapsContact.Ascent RG OPE PhysicalNext.Repeat.Legato
open Maxwell XSpace XSpace.Normalize FVA2 FVA2.Register
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open scoped Topology Classical
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G){Y:(Bel R.family.book).Hierarchy}

include Z in
theorem own (lead:Leading F J)(d:ℕ):
    ∃B:ℝ,0≤B ∧ ∀ᶠr in trail,∀v:S.Field d,Ascent.cost F d r v ≤ B*‖(J r d).symm v‖:=by
  obtain ⟨B,hB,wise⟩:=WilsonNormalizedReflectedForm.uniform F J Z.store lead d zero_le_one
  refine ⟨B,hB,?_⟩
  filter_upwards [wise] with r paid y
  let x:=(J r d).symm y
  by_cases zero:x=0
  · have hy:y=0:=by rw [←(J r d).apply_symm_apply y];change (J r d) x=0;rw [zero,map_zero]
    simpa only [hy,Ascent.cost_zero,map_zero,norm_zero,mul_zero] using le_refl (0:ℝ)
  have pos:0<‖x‖:=norm_pos_iff.mpr zero
  let c:ℂ:=‖x‖
  have cn:‖c‖=‖x‖:=Complex.norm_of_nonneg pos.le
  have cp:c≠0:=by simpa only [c,ne_eq,Complex.ofReal_eq_zero] using pos.ne'
  have unit:‖c⁻¹ • x‖≤1:=by rw [norm_smul,norm_inv,cn,inv_mul_cancel₀ pos.ne']
  have fee:=paid false (c⁻¹ • x) unit
  change Ascent.cost F d r ((J r d) (c⁻¹ • x))≤B at fee
  have he:c • J r d (c⁻¹ • x)=y:=by rw [map_smul,smul_smul,mul_inv_cancel₀ cp,one_smul];exact (J r d).apply_symm_apply y
  calc
    _=‖c‖*Ascent.cost F d r (J r d (c⁻¹ • x)):=by rw [←Ascent.cost_hom,he]
    _≤ B*‖x‖:=by rw [cn,mul_comm B];exact mul_le_mul_of_nonneg_left fee pos.le

theorem original (lead:Leading F J)(owed:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)
    (simple:G.Simple)(d:ℕ):
    ∃C:ℝ,0≤C ∧ ∀ᶠt in trail,∀s∈Ioc (0:ℝ) 1,∀v:RG17.Free R.family d,
      Ascent.cost F d (s*t) (homogeneous F J Z t d v)≤C*s^(-(d:ℝ)-1)*‖v‖:=by
  obtain ⟨B,hB,own⟩:=own F J Z lead d
  obtain ⟨K,hK,move⟩:=WilsonPhysicalExteriorFrame.between F d J lead 1 one_pos
  obtain ⟨U,hU,aim⟩:=WilsonMacroscopicRichTwoDatePivot.bounded F J Z lead owed simple d
  obtain ⟨δ,hδ,admitted⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp own
  refine ⟨B*K*U,mul_nonneg (mul_nonneg hB (zero_le_one.trans hK)) hU,?_⟩
  filter_upwards [move,aim,show ∀ᶠt in trail,t∈Ioc (0:ℝ) δ from
    mem_nhdsGT_iff_exists_Ioc_subset.mpr ⟨δ,hδ,subset_refl _⟩] with t lift original ht s hs v
  have small:s*t∈Ioc (0:ℝ) δ:=⟨mul_pos hs.1 ht.1,(mul_le_of_le_one_left ht.1.le hs.2).trans ht.2⟩
  have top:‖(J t d).symm (homogeneous F J Z t d v)‖≤U*‖v‖:=original v
  exact (admitted small _).trans ((mul_le_mul_of_nonneg_left ((lift s hs _).trans
    (mul_le_mul_of_nonneg_left top (mul_nonneg (zero_le_one.trans hK) (Real.rpow_nonneg hs.1.le _)))) hB).trans_eq (by ring))

end YM.Integration.WilsonMovingForkFarCost
