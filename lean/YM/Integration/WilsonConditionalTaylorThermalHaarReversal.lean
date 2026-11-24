import YM.Integration.WilsonConditionalTaylorThermalLogHaar

/-! Haar inversion and the actual injective exponential slice force the
given local chart density to be even. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalHaarReversal
open Set Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport PertExtension
open scoped Classical BigOperators Topology
variable {G : Gauge} (P : ChartRatio G) (R : LocalRatio P)

def weight (x : G.Color) := ENNReal.ofReal (P.scale*P.J x)

include R

theorem charged {C : Set G.Color} (hc : MeasurableSet C) (inside : C⊆Metric.ball 0 P.radius) :
    ∫⁻x in C,weight P x ∂volume = G.probHaar (G.lieExp '' C) := by
  let B := Metric.ball (0:G.Color) P.radius
  have det : MeasurableSet (G.lieExp '' C) := hc.image_of_continuousOn_injOn
    G.lieExp_cont.continuousOn (R.inject.mono inside)
  have weak := congrArg (fun m : Measure G.El=>m (G.lieExp '' C)) R.actual
  rw [Measure.map_apply G.lieExp_cont.measurable det,Measure.restrict_apply det,
    inter_eq_left.mpr (image_mono inside),withDensity_apply _ (G.lieExp_cont.measurable det),
    Measure.restrict_restrict (G.lieExp_cont.measurable det)] at weak
  have window : G.lieExp ⁻¹' (G.lieExp '' C) ∩ B=C := by
    ext x;constructor
    · rintro ⟨⟨y,hy,e⟩,hx⟩;exact R.inject (inside hy) hx e ▸ hy
    · intro hx;exact ⟨⟨x,hx,rfl⟩,inside hx⟩
  rw [window] at weak
  exact weak

theorem reflected {C : Set G.Color} (hc : MeasurableSet C) (inside : C⊆Metric.ball 0 P.radius) :
    ∫⁻x in C,weight P (-x) ∂volume = ∫⁻x in C,weight P x ∂volume := by
  let neg : G.Color→G.Color := fun x=> -x
  have hm : Measurable neg := measurable_neg
  have also : neg ⁻¹' C⊆Metric.ball 0 P.radius := by
    intro x hx
    have h := inside hx
    simpa [neg,Metric.mem_ball,dist_zero_right] using h
  have image_ : G.lieExp '' (neg ⁻¹' C)=(fun z:G.El=>z⁻¹) ⁻¹' (G.lieExp '' C) := by
    ext z;constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨-x,hx,Work.F03.exp_neg_color (G:=G) x⟩
    · rintro ⟨x,hx,hz⟩
      refine ⟨-x,?_,?_⟩
      · simpa [neg] using hx
      · rw [Work.F03.exp_neg_color,hz,inv_inv]
  have det := hc.image_of_continuousOn_injOn G.lieExp_cont.continuousOn (R.inject.mono inside)
  have double : neg ⁻¹' (neg ⁻¹' C)=C := by ext x;simp [neg]
  have shift := ((Measure.measurePreserving_neg (volume : Measure G.Color)).restrict_preimage (hm hc)).lintegral_comp
    (R.borel.const_mul P.scale).ennreal_ofReal
  change (∫⁻x in neg ⁻¹' (neg ⁻¹' C), weight P (-x) ∂volume)=∫⁻x in neg ⁻¹' C,weight P x ∂volume at shift
  rw [double,charged P R (hm hc) also,image_,(Measure.measurePreserving_inv G.probHaar).measure_preimage det.nullMeasurableSet] at shift
  exact shift.trans (charged P R hc inside).symm

theorem original : EqOn (fun x=>P.J (-x)) P.J (Metric.ball 0 P.radius) := by
  let B := Metric.ball (0:G.Color) P.radius
  let ν := (volume : Measure G.Color).restrict B
  have mh : Measurable (weight P) := (R.borel.const_mul _).ennreal_ofReal
  have mn : Measurable (fun x=>weight P (-x)) := mh.comp measurable_neg
  have equal : ν.withDensity (fun x=>weight P (-x))=ν.withDensity (weight P) := by
    ext C hc
    rw [withDensity_apply _ hc,withDensity_apply _ hc]
    change (∫⁻x in C,weight P (-x) ∂volume.restrict B)=∫⁻x in C,weight P x ∂volume.restrict B
    rw [Measure.restrict_restrict hc]
    exact reflected P R (hc.inter Metric.isOpen_ball.measurableSet) inter_subset_right
  have dens := (withDensity_eq_iff_of_sigmaFinite mn.aemeasurable mh.aemeasurable).mp equal
  have mirror (x : G.Color) (hx : x∈B) : -x∈B := by simpa [B,Metric.mem_ball,dist_zero_right] using hx
  have localEq : (fun x=>P.J (-x))=ᵐ[ν]P.J := by
    filter_upwards [dens,ae_restrict_mem (μ:=(volume:Measure G.Color)) Metric.isOpen_ball.measurableSet] with x hx hB
    have eq := congrArg ENNReal.toReal hx
    rw [weight,weight,ENNReal.toReal_ofReal (mul_pos R.scale (R.pos _ (mirror _ hB))).le,
      ENNReal.toReal_ofReal (mul_pos R.scale (R.pos _ hB)).le] at eq
    exact mul_left_cancel₀ R.scale.ne' eq
  apply Measure.eqOn_open_of_ae_eq (μ:=(volume:Measure G.Color)) localEq Metric.isOpen_ball
  · exact fun x hx=>((R.germ _ (mirror _ hx)).continuousAt.comp continuous_neg.continuousAt).continuousWithinAt
  · exact fun x hx=>(R.germ _ hx).continuousAt.continuousWithinAt

end YM.Integration.WilsonConditionalTaylorThermalHaarReversal
