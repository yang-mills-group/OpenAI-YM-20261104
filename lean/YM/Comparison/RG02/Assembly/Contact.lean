import YM.Comparison.RG02.Assembly.Vertices
/-! Germ restrictions for the extra Fk generators (curried actual log chart etc.). -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Assembly
open Function Filter MeasureTheory
open PertExtension.Series Order
open scoped Topology BigOperators ContDiff Classical

variable {W X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {w : W} {p i k: ℕ}

lemma contact_right (L : W→L[ℝ] X) {f : X→ Y} (h : ContDiffAt ℝ i f (L w)) :
   iteratedFDeriv ℝ i (f ∘ L) w = (iteratedFDeriv ℝ i f (L w)).compContinuousLinearMap fun _=> L := by
  obtain ⟨s,hs,he⟩ := h.contDiffOn le_rfl (by simp)
  obtain ⟨r,hr,hb⟩:= Metric.mem_nhds_iff.mp hs
  have hx:=Metric.mem_ball_self (x:=L w) hr
  have ho := Metric.isOpen_ball (x:=L w) (ε:=r)
  have hr' := L.iteratedFDerivWithin_comp_right (he.mono hb) ho.uniqueDiffOn (ho.preimage L.continuous).uniqueDiffOn hx (le_refl (i:WithTop ℕ∞))
  rwa [iteratedFDerivWithin_of_isOpen _ (ho.preimage L.continuous) (Set.mem_preimage.mpr hx), iteratedFDerivWithin_of_isOpen _ ho hx] at hr'
lemma jet_continuous_right (L : W →L[ℝ] X) {f : X→ Y} (h : ContDiffAt ℝ i f 0) (a : W) :
    jet (f ∘ L) i a=jet f i (L a) := by
  unfold jet; rw [contact_right L (show ContDiffAt ℝ i f (L 0) from L.map_zero.symm ▸ h),L.map_zero]
  rfl

/-- Grade lower bound phrased on the actual fields, rather than on the projection readout. -/
structure GradeAt (k : ℕ) (f : X→Y) : Prop where
  smooth : ContDiffAt ℝ ω f 0
  vanish (i : ℕ) : i<k → iteratedFDeriv ℝ i f 0=0

namespace GradeAt
variable {f : X→Y}
lemma jet_z (h : GradeAt k f) (x : X) (hk : i<k) : jet f i x=0 := by rw [jet,h.vanish _ hk]; simp

lemma coarse {g : W→X} (h : GradeAt k f) (hv : ContDiffAt ℝ ω g 0) (he : g 0=0) : GradeAt k (f ∘ g) := by
  have hf : ContDiffAt ℝ ω f (g 0) := he.symm ▸ h.smooth
  constructor
  · exact hf.comp _ hv
  intro i hi; rw [iteratedFDeriv_comp hf hv le_top, he,FormalMultilinearSeries.taylorComp]; refine Finset.sum_eq_zero fun c _ => ?_
  ext x
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
  rw [h.vanish _ (c.length_le.trans_lt hi)]; rfl

lemma depends {f' : X→Y} (h : GradeAt k f) (he : f =ᶠ[𝓝 0] f') : GradeAt k f' :=
  ⟨h.smooth.congr_of_eventuallyEq he.symm, fun i hi=> (he.symm.iteratedFDeriv ℝ i).eq_of_nhds.trans (h.vanish i hi)⟩
lemma add {f' : X→Y} (h : GradeAt k f) (H : GradeAt k f') : GradeAt k (f+f') := by
  refine ⟨h.smooth.add H.smooth,fun i hi=>?_⟩
  rw [iteratedFDeriv_add_apply (h.smooth.of_le le_top) (H.smooth.of_le le_top), h.vanish i hi, H.vanish i hi, add_zero]
lemma sub {f' : X→Y} (h : GradeAt k f) (H : GradeAt k f') : GradeAt k (f-f') := by
  refine ⟨h.smooth.sub H.smooth,fun i hi=>?_⟩
  rw [iteratedFDeriv_sub_apply (h.smooth.of_le le_top) (H.smooth.of_le le_top), h.vanish i hi, H.vanish i hi, sub_zero]
theorem lower (h : GradeAt k f) (hl : i ≤ k) : GradeAt i f := ⟨h.smooth, fun j hj=> h.vanish j (hj.trans_le hl)⟩
lemma add_min {f':X→Y} (h : GradeAt k f) (hx : GradeAt i f') : GradeAt (min k i) (f+f') := (h.lower (min_le_left ..)).add (hx.lower (min_le_right ..))
lemma grade_zero (k : ℕ) : GradeAt k (fun _:X=>(0:Y)) := by
  refine ⟨contDiffAt_const,fun i hi=> ?_⟩
  cases i with
  | zero => ext x; rw [iteratedFDeriv_zero_apply]; rfl
  | succ j=> exact congr_fun (iteratedFDeriv_const_of_ne (by omega : j+1 ≠ 0) (0:Y)) _
end GradeAt
end YM.Comparison.RG02.Assembly
