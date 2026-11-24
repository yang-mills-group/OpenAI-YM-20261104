import YM.Integration.WilsonPublicOutputDetector

/-! The engineering power acts on the relative measured coordinate. The finite
public change at the near reporting radius has a uniformly bounded inverse. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPublicOutputFrame
open Filter Set Table Spec OPE PhysMS Trace.Pilot Climb Extra.FD
open FVA2 FVA2.Register PhysicalNext.Repeat.Legato WilsonMacroscopicRichTwoDatePivot
open WilsonPositionHomogeneousFrame
open private cost clm_bound from YM.Integration.WilsonOrdinaryMixedDetectors
open scoped Classical Topology BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (Z : WilsonPrescription G)

/-- This equality keeps the full measured change of field, including its lower coordinates,
before applying each exact engineering factor. -/
theorem engineering (h : ℕ) (τ ρ : ℝ) (hp : 0 < ρ)
    (e : (Bel R.family.book).Field h) (i : Fin ((recorded R.family.labels h).m+1)) :
    let B := recorded R.family.labels h
    B.b.coord i ((J τ h).symm (J (ρ*τ) h e)) =
      (ρ : ℂ)^((B.w i).1) * B.b.coord i (Frame.cocycle h J τ ρ hp e) := by
  intro B
  let x := Frame.cocycle h J τ ρ hp e
  have eq : (J τ h).symm (J (ρ*τ) h e) = Pert.Scale.gear R.family.labels h ρ x := by
    apply (J τ h).injective
    rw [LinearEquiv.apply_symm_apply,Frame.cocycle_value]
  rw [eq]
  change B.b.coord i (Pert.Scale.gear R.family.labels h ρ x) = (ρ:ℂ)^(B.w i).1 * B.b.coord i x
  conv_lhs => rw [←B.b.sum_repr x, map_sum, map_sum]
  simp [map_smul,Pert.Scale.rare,Module.Basis.coord_apply,Finsupp.single_apply,smul_eq_mul,mul_comm]

theorem normalized {Y : (Bel R.family.book).Hierarchy}
    (lead : Leading F J) (owed : ∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d)
    (simple : G.Simple) (h : ℕ) :
    ∀ᶠ r in trail, ∀ y : S.Field h,
      ‖(homogeneous F J Z r h).symm y‖ ≤ 2*‖(J r h).symm y‖ := by
  let b := Module.finBasis ℝ ((Bel R.family.book).Field h)
  let m := cost b
  have mn : 0 ≤ m := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let δ := (2*(m+1))⁻¹
  have dp : 0 < δ := by dsimp only [δ]; positivity
  have columns : ∀ᶠ r in trail, ∀ i, ‖active F J Z r h (b i)-b i‖ ≤ δ := by
    apply eventually_all.mpr
    intro i
    have cv : Tendsto (fun r => active F J Z r h (b i)-b i) trail (𝓝 0) := by
      simpa only [sub_self] using (field F J Z lead owed simple h (b i)).sub (tendsto_const_nhds (x:=b i))
    have low : ‖(0 : (Bel R.family.book).Field h)‖ < δ := by simpa only [norm_zero]
    exact cv.norm.eventually (ge_mem_nhds low)
  filter_upwards [columns] with r fit y
  let v := (homogeneous F J Z r h).symm y
  let D := (((active F J Z r h).toLinearMap - LinearMap.id).toContinuousLinearMap).restrictScalars ℝ
  have diff := (D.le_opNorm v).trans (mul_le_mul_of_nonneg_right (clm_bound b D dp.le fit) (norm_nonneg _))
  have half : m*δ ≤ (1/2:ℝ) := by
    dsimp only [δ]
    rw [←div_eq_mul_inv,div_le_iff₀ (by positivity)]
    linarith
  have small : ‖active F J Z r h v - v‖ ≤ (1/2:ℝ)*‖v‖ :=
    diff.trans (mul_le_mul_of_nonneg_right half (norm_nonneg _))
  have near : ‖v‖ ≤ ‖active F J Z r h v-v‖ + ‖active F J Z r h v‖ :=
    calc _ = ‖(v-active F J Z r h v)+active F J Z r h v‖ := by rw [sub_add_cancel]
         _ ≤ _ := by rw [norm_sub_rev]; exact norm_add_le _ _
  have atDate : active F J Z r h v = (J r h).symm y := by
    simp only [active,LinearEquiv.trans_apply,v,LinearEquiv.apply_symm_apply]
  rw [←atDate]
  change ‖v‖ ≤ _
  linarith
end YM.Integration.WilsonPublicOutputFrame
