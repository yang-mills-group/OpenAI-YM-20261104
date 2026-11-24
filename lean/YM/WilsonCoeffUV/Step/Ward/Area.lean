import YM.WilsonCoeffUV.Step.Ward.ReTree
import YM.PertExtension.BareChart
/-! Real area comparison in the necessary slice only. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power
open MeasureTheory Wilson Lattice Laurent Exterior Bloch Matrix Precision RG Blue
open Next.Free FreeResolvent Tree Filter Metric Function Set
open YM.PertExtension.Chart (tangent physical expLinks fee jacobian small chamber)
open scoped Topology ContDiff BigOperators ENNReal
variable {c f n : Side}{G:Gauge}

private lemma zoom_fee {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][ProperSpace E]
    [MeasurableSpace E][BorelSpace E] (μ:Measure E)[IsFiniteMeasureOnCompacts μ][μ.IsOpenPosMeasure]
    {f g:E→ℝ}{x}{Ω:Set E}(hΩ:Ω∈ 𝓝 x) (hf:ContinuousAt f x)(hg:ContinuousAt g x)(h:0≤g x)
    (hh:∀ C:Set E,IsCompact C→C⊆Ω→ (∫⁻ y in C, ENNReal.ofReal (f y) ∂μ)≤∫⁻ y in C, ENNReal.ofReal (g y) ∂μ) : f x≤g x := by
  by_contra! ht
  obtain ⟨b,hb,H⟩:=exists_between ht; obtain ⟨a,ha,hA⟩:=exists_between H
  have hΩ': ∀ᶠ y in 𝓝 x, y∈Ω ∧ g y < b ∧ a < f y := (show ∀ᶠ y in 𝓝 x,y∈Ω from hΩ).and ((hg.eventually (gt_mem_nhds hb)).and (hf.eventually (lt_mem_nhds hA)))
  obtain ⟨r,hr,hR⟩ := nhds_basis_closedBall.mem_iff.mp hΩ'
  let C:=closedBall x r; have hx := isCompact_closedBall x r
  have hy y (hy:y∈C) : y∈Ω ∧ g y<b ∧ a<f y:= hR hy
  have hm : 0<μ C := lt_of_lt_of_le (isOpen_ball.measure_pos μ ⟨_,mem_ball_self hr⟩) (measure_mono ball_subset_closedBall)
  apply (hh C hx (fun y hy'=> (hy _ hy').1)).not_gt
  calc (∫⁻ y in C, ENNReal.ofReal (g y) ∂μ) ≤ ∫⁻ _ in C,ENNReal.ofReal b ∂μ := setLIntegral_mono' hx.measurableSet fun i h'=> ENNReal.ofReal_le_ofReal (hy _ h').2.1.le
       _ < ∫⁻ _ in C,ENNReal.ofReal a ∂μ:= by simp only [lintegral_const, Measure.restrict_apply_univ]; exact ENNReal.mul_lt_mul_left hm.ne' hx.measure_lt_top.ne ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (h.trans hb.le)).mpr ha)
       _ ≤ ∫⁻ y in C, ENNReal.ofReal (f y) ∂μ:=setLIntegral_mono' hx.measurableSet fun i h'=> ENNReal.ofReal_le_ofReal (hy _ h').2.2.le

section
variable {U Z:Type}[Fintype U][NormedAddCommGroup Z][NormedSpace ℝ Z]
private lemma scope_j {r:ℝ}{P:ChartRatio G}(h:LocalRatio P)(hr:0<r)(he:r<small G P) :
   Set.InjOn (expLinks G U) (Metric.ball 0 r):= by
  intro u hu v hv H
  have hm x (hx':x∈ ball (0:U→G.Color) r)(i:U): x i ∈ ball 0 P.radius := by
    rw [ball_pi _ hr] at hx';
    exact ball_subset_ball ((he.trans_le ((min_le_left _ _))).trans_le (half_le_self h.patch.le)).le (hx' i trivial)
  funext i; exact h.inject (hm _ hu _) (hm _ hv _) (congr_fun H i)
private lemma combined_area {r:ℝ}{P:ChartRatio G}(h:LocalRatio P)(hr:0<r)(he:r<small G P)
    (C:Set (U→G.Color))(hc:IsCompact C)(ht:C⊆ball 0 r) : physical G U (expLinks G U '' C) =∫⁻ y in C, ENNReal.ofReal (jacobian P y) ∂tangent G U:=by
  let Ω := expLinks G U '' C
  have hy : MeasurableSet Ω := (hc.image (show Continuous (expLinks G U) from continuous_pi fun i=> G.lieExp_cont.comp (continuous_apply i))).measurableSet
  have hp:= PertExtension.Chart.Ratio.combined (U:=U) h he hr
  have hx : expLinks G U ⁻¹' Ω ∩ ball 0 r=C := by
    apply Set.Subset.antisymm
    · rintro i ⟨⟨j,hj,e⟩,hi⟩; rw [← scope_j h hr he (ht hj) hi e]; exact hj
    intro i hi; exact ⟨Set.mem_image_of_mem _ hi, ht hi⟩
  have hv: Ω⊆chamber G U r := by
    rintro _ ⟨x,hx,rfl⟩; intro i _; apply Set.mem_image_of_mem; have h := ht hx; rw [ball_pi _ hr] at h; exact h i trivial
  have hu := hp.measure_preimage hy.nullMeasurableSet
  rw [Measure.restrict_apply hy,inter_eq_left.mpr hv,withDensity_apply _ (hp.measurable hy),Measure.restrict_restrict (hp.measurable hy),hx] at hu
  exact hu.symm

/-- Absolute det, at every point sufficiently near zero, holding parameter fixed. -/
theorem areaP {P:ChartRatio G}(h:LocalRatio P)(F:(U→G.Color) × Z → U → G.Color)(f0:F 0=0)
    (k:Z → (U→G.El) → U→G.El)
    (he:∀ z,MeasurePreserving (k z) (physical G U) (physical G U))
    (hk:∀ z,Injective (k z)) (hf:ContDiffAt ℝ ω F 0)
    (hF: ∀ᶠ x:(U→G.Color) × Z in 𝓝 0,expLinks G U (F x) = k x.2 (expLinks G U x.1)) :
    ∀ᶠ x:(U→G.Color) × Z in 𝓝 0, |(fderiv ℝ (fun y=>F (y,x.2)) x.1).det| *jacobian P (F x)=jacobian P x.1 := by
  let μ:=tangent G U
  let r:=small G P /2; have hr :0< r:=half_pos (PertExtension.Chart.Ratio.small_pos h); have hr': r<small G P:=half_lt_self (PertExtension.Chart.Ratio.small_pos h)
  let Ω := {x:(U→G.Color) × Z | x.1∈ ball 0 r ∧ F x∈ ball 0 r ∧ ContDiffAt ℝ ω F x ∧ expLinks G U (F x)=k x.2 (expLinks G U x.1)}
  have hΩ: Ω∈ 𝓝 0:= by
    have he : ∀ᶠ x in 𝓝 0,F x∈ball 0 r:=hf.continuousAt.eventually (by rw [f0]; exact ball_mem_nhds _ hr)
    filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (x:=(0:(U→G.Color) × Z)) (Metric.ball_mem_nhds (0:U→G.Color) hr),he,hf.eventually (by simp), hF] with x ha hb hh hc
    exact ⟨ha,hb,hh,hc⟩
  have hj: ∀ᶠ u in 𝓝 (0:U→G.Color), ContDiffAt ℝ ω (jacobian P) u := (PertExtension.Chart.Ratio.jacobian_smooth h).eventually (by simp)
  have hY:=hf.continuousAt.tendsto; rw [f0] at hY
  filter_upwards [eventually_eventually_nhds.mpr hΩ,hY.eventually hj,(continuous_fst.tendsto (0:(U→G.Color) × Z)).eventually hj] with x hx hx' hx₀
  let f (i:U→G.Color):= F (i,x.2); let A:= (fun y=>(y,x.2)) ⁻¹' Ω
  have hh:A ∈ 𝓝 x.1 := (continuous_id.prodMk continuous_const).continuousAt (by exact hx)
  have hA (v) (h:v∈A) := (show (v,x.2)∈Ω from h)
  let J := fun i=> |(fderiv ℝ f i).det| *jacobian P (f i)
  have ht i (h:i∈A) : ContDiffAt ℝ ω f i := (hA i h).2.2.1.comp (f:=fun y=>(y,x.2)) i (contDiffAt_id.prodMk contDiffAt_const)
  have hq : ContDiffAt ℝ ω f x.1:= ht _ (mem_of_mem_nhds hh)
  have hJ : ContinuousAt J x.1:= ((ContinuousLinearMap.continuous_det.continuousAt.comp (hq.fderiv_right (m:=ω) (by simp)).continuousAt).abs).mul (ContinuousAt.comp (g:=jacobian P) (f:=f) (by apply hx'.continuousAt) hq.continuousAt)
  have hL (C:Set (U→G.Color))(hc:IsCompact C)(hC:C⊆A) : (∫⁻ y in C,ENNReal.ofReal (J y) ∂tangent G U)=∫⁻ y in C,ENNReal.ofReal (jacobian P y) ∂tangent G U := by
    have hsc : IsCompact (f '' C) := hc.image_of_continuousOn (fun x hx=> (ht x (hC hx)).continuousAt.continuousWithinAt)
    have hv: C ⊆ ball 0 r := fun i hi=> (hA _ (hC hi)).1
    have hw: f '' C ⊆ ball 0 r:= by rintro _ ⟨x,hx,rfl⟩; exact (hA _ (hC hx)).2.1
    have hb x (h:x∈C): expLinks G U (f x) = k _ (expLinks G U x):= (hA _ (hC h)).2.2.2
    have hy : k x.2 ⁻¹' (expLinks G U '' (f '' C)) = expLinks G U '' C := by
      ext i; constructor
      · rintro ⟨_,⟨y,hh,rfl⟩,h⟩; exact ⟨y,hh,hk x.2 ((hb y hh).symm.trans h)⟩
      rintro ⟨y,hh,rfl⟩; rw [Set.mem_preimage,← hb y hh]; exact mem_image_of_mem _ (mem_image_of_mem _ hh)
    have heq := (he x.2).measure_preimage (hsc.image (show Continuous (expLinks G U) from continuous_pi fun i=> G.lieExp_cont.comp (continuous_apply i))).measurableSet.nullMeasurableSet
    rw [hy, combined_area h hr hr' _ hsc hw,combined_area h hr hr' _ hc hv,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul (tangent G U) hc.measurableSet (fun x hx=>(ht x (hC hx)).differentiableAt (by simp)|>.hasFDerivAt.hasFDerivWithinAt) ?hin] at heq
    unfold J; simp only [ENNReal.ofReal_mul (abs_nonneg _)]; exact heq.symm
    intro i hi j hj H; apply scope_j h hr hr' (hv hi) (hv hj); apply hk x.2
    rw [←hb i hi,←hb j hj,H]
  refine le_antisymm (zoom_fee (tangent G U) hh hJ hx₀.continuousAt (PertExtension.Chart.jacobian_nonneg _) (fun C c e=> (hL C c e).le))
    (zoom_fee (tangent G U) hh hx₀.continuousAt hJ (mul_nonneg (abs_nonneg _) (PertExtension.Chart.jacobian_nonneg _)) (fun C c e=> (hL C c e).ge))
end
end YM.WilsonCoeffUV.Power
