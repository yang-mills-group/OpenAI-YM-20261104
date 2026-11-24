import YM.RGLocalTaylor.Engine.Slice

/-!
# Derivatives of the true integrated molecule including all holding/switch effects

Do the chart change of variables then use the qualitative (`Zest`) property
of the licensed probe. As in `Mercury.boosts`, get a grip on all state-dependent
integrations on an actual OPEN neighborhood, to then do the needed pointwise
pricing. This already includes polynomial, indicator and exponential partners
when those are retained by the particular probe. No operation on the actual
coarse flag function during differentiation. Also justify linearity ON that germ;
don't assume all off-healthy real fields in `slice` are integrable in all models.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

namespace Fits
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {V : E → Config G c} {x : E} {I : Finset (Bond f)} {u : Support c} (hX : X.x=s) (hM : X.manifest) (hK : X.width=o.K)
    (hg : Glass P X V x j W) (hC : Canary G A b) (he : 8*o.a*Pressure.fiery G s L ≤ A/2)

variable {r : Insert T} (h : Fits H r u j)
include h hX hM hK hg hC he

lemma reaches :
    let m:=(F.order G).prod X.dice; let g v:= r.rhythmic I A R.beta X (V v)
    Meristem g x m j ∧ ∀ᶠ y in 𝓝 x, Integrable (g y) m := by
  intro m g
  have heq:= H.laws.data; have hΘ:= h.near X hX hK hM E V x hC he hg
  have hM := heq.localP F X hX hK hM
  let A' := lensS I G; let U i:=circuit A' (vary X (V i)).relating; let V':= circuit A' X.relating
  have hx: U x=V' := by unfold U V'; rw [hg.lifts]; rfl
  have hF:= hM.sails.fullC; have hU' : V'.PosDef := hF.submatrix Subtype.val_injective
  have hV:= own_mat hM.sails I
  have hs : Bottom V'⁻¹ (1+payE o.eta o.gap o.ample (tubularPrice G L))⁻¹ :=
    Control.lower_inverse hV.relented hV.weather.1.le hV.fuel hV.symmetry hV.ground hV.down.le hV.initial.1
  let X'(t:F.Slice G × Air f G):= X.wrapY t.1; let w t v:= course (X' t) A R.beta t.2 (V v)
  let z(t:F.Slice G × Air f G):= Pond.swim A' t.2; have hZ : MeasurePreserving z m (sweep V') := by
    have hs := (Pond.orbit hF.posSemidef A')
    apply hs.comp (show MeasurePreserving _ m X.dice from _); exact MeasureTheory.measurePreserving_snd
  let Z t i:= Pond.swim A' (w t i)
  obtain ⟨hΞ,hω⟩:= Glass.towers (U:=fun i:F.Slice G × Air f G=> i.2) (Y:=fun i=> i.1) hg hM.sails.room hC I H.laws.intake.positive
  obtain ⟨B,hB,hk,hP⟩:= winglet (A:=U) (Z:=z) (V:=Z) (hx.symm ▸ hU') (hx.symm ▸ hs) (inv_pos.mpr hV.fuel)
    (fun i j=>hg.relate i.val j.val) hω
  obtain ⟨J,hJ,hH⟩:= hΞ.post
  obtain ⟨K,h₁,h₂⟩:= hΘ.post
  refine Meristem.points g m ?_ ?_
  · let K' t := (J*B (z t)*K)*(1+((1+1)+1))^j
    rw [hx] at hk
    have hb : Integrable (B ∘ z) m := (hZ.integrable_comp hB.aestronglyMeasurable).2 hk
    refine ⟨K',((hb.const_mul J).mul_const K).mul_const _,?_⟩
    filter_upwards [hH,h₂,hP] with i hi h hh s
    have hx' := hh s
    rw [hx] at hx'
    exact (((hi s).paints hx').paints (h s)).trim
  obtain ⟨s,h'⟩:= hg.sails; filter_upwards [nearby X hC hg.lifts h'] with y hh'
  exact h.onCourse_meas hX hK (V y) hC hh' I measurable_fst measurable_snd

lemma slideToCourse (Y : Support c) (hy : u ⊆ Y) :
    let m:=(F.order G).prod X.dice; let I:= edgesM S Y X.B
    let g v:= r.rhythmic I A R.beta X (V v)
    (fun v=> r.onSlice (podium S G Y X.B) (vary X (V v))) =ᶠ[𝓝 x] fun v=>∫ y,g v y ∂m := by
  intro m I g; obtain ⟨_,ht⟩:= h.reaches (I:=I) hX hM hK hg hC he
  obtain ⟨v,hv⟩:= hg.sails; have he:= H.laws.data
  filter_upwards [ht,nearby X hC hg.lifts hv] with y hy' hY
  rw [← chargedU, integral_prod _ hy']
  exact h.slice_eq hX hK (V y) hC hY (he.localP F X hX hK hM).sails.fullC Y hy

section linear
omit h
variable {ι : Type} {w : Finset ι} {f' : ι → Insert T} (hA : ∀ i∈w,Fits H (f' i) u j)
include hA
lemma add_near : ∀ᶠ y in 𝓝 x,
    (Insert.together w f').onSlice (podium S G u X.B) (vary X (V y)) =
      ∑ i∈w,(f' i).onSlice (podium S G u X.B) (vary X (V y)) := by
  let m:=(F.order G).prod X.dice; let I:= edgesM S u X.B
  let g (q : Insert T) v:= q.rhythmic I A R.beta X (V v)
  let r (q : Insert T) v:= q.onSlice (podium S G u X.B) (vary X (V v)); let q:= Insert.together w f'
  have hL(F':Insert T)(hz:Fits H F' u j):= hz.slideToCourse hX hM hK hg hC he _ (Finset.Subset.refl u)
  have hP(i:ι)(hi:i∈w):∀ᶠ y in 𝓝 x, r (f' i) y=(∫ z, g (f' i) y z ∂m) ∧ Integrable (g (f' i) y) m:=
    (hL _ (hA i hi)).and ((hA i hi).reaches (I:=I) hX hM hK hg hC he).2
  filter_upwards [(eventually_all_finset w).mpr hP,hL q (Fits.together hA)] with y hy hh
  change r q y=_
  change r q y=∫ z,g q y z ∂m at hh
  rw [hh,show g q y=(fun z=>∑ i∈w,g (f' i) y z) from ?_, integral_finsetSum w fun i hi=>(hy i hi).2]
  · exact Finset.sum_congr rfl (fun i hi=>(hy i hi).1.symm)
  funext z; exact Finset.mul_sum ..

end linear
end Fits
end YM.RGLocalTaylor
