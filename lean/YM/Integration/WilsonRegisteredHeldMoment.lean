import YM.Integration.WilsonRegisteredCenteredReading
import YM.Integration.WilsonCoherentLowerExperiment

/-! Joint measurability of dated, centered observables and their true
held expectations. The mark may depend on the actual lower configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredHeldMoment
open Function Filter Set MeasureTheory Metric Lattice RG Wilson Tree Precision PertExtension
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato MSbar.Heath OPE.Therm
open OriginalMarkedRunAction WilsonCoherentForestMeasure WilsonCoherentForestReadout
open WilsonRegisteredCenteredReading
open private real_test from YM.Integration.WilsonRegisteredDegreeFourCovariance
open scoped Classical Topology
variable {G:Gauge} (R:Run G) {m N per:ℕ}
local notation "c" => R.family.side m per
local notation "n" => R.family.side (m+1) per

theorem observed (live:m<N) {f:Config G c × Config G n→ℝ} (hf:Envelope f) :
    Envelope (fun V=>actualAverage R.family (N:=N) (fun U=>f (V,U)) V) := by
  have w:=ActualWilsonConditionalRoots.density_meas R.family (p:=per) R.makes live
  have joined:=w.mul hf.meas
  obtain ⟨M,hM⟩:=hf.cost
  exact ⟨joined.stronglyMeasurable.integral_prod_right'.measurable,M,
    fun V=>actualAverage_norm_le R.family R.makes live (fun U=>hM (V,U)) V⟩

theorem enclosed {f:Config G c × Config G n→ℝ} (S:Set (Config G n)) (ms:MeasurableSet S) (ef:Envelope f) :
    Envelope (fun z:Config G c × Config G n=>S.indicator (fun U=>f (z.1,U)) z.2) := by
  let T:Set (Config G c × Config G n):=Prod.snd ⁻¹' S
  have same:(fun z:Config G c × Config G n=>S.indicator (fun U=>f (z.1,U)) z.2)=T.indicator f:=by
    funext z
    by_cases h:z.2∈S
    · rw [indicator_of_mem h,indicator_of_mem (show z∈T from h)]
    · rw [indicator_of_notMem h,indicator_of_notMem (show z∉T from h)]
  rw [same]
  exact ⟨ef.meas.indicator (measurable_snd ms),ef.cost.choose,fun x=>(norm_indicator_le_norm_self f x).trans (ef.cost.choose_spec x)⟩

theorem centered_joint (live:m+1≤N) (ref:R.family.ref 4 ≤ m+1) (v:R.family.label 4) (o:Site n) (η:ℂ→L[ℝ]ℝ):
    Envelope (fun z:Config G c × Config G n=>centered R live v o η z.1 z.2) := by
  have reg:=WilsonMeasuredInheritedGauge.occupied R.family R.makes live v ((R.family.S.toDepth live per).embed o)
  dsimp only at reg
  rw [WilsonInheritedRegisteredField.original (C:=R.family) R.makes live ref v o] at reg
  have ef:Envelope (source R live v o η):=real_test reg.1 η
  have af:=WilsonCoherentEarlier.averaged R.family R.makes live ef
  have fv:Envelope (fun z:Config G c × Config G n=>source R live v o η z.2):=
    ⟨ef.meas.comp measurable_snd,ef.cost.choose,fun z=>ef.cost.choose_spec z.2⟩
  have av:Envelope (fun z:Config G c × Config G n=>actualAverage R.family (N:=N) (source R live v o η) z.1):=
    ⟨af.meas.comp measurable_fst,af.cost.choose,fun z=>af.cost.choose_spec z.1⟩
  change Envelope (fun z:Config G c × Config G n=>source R live v o η z.2-actualAverage R.family (N:=N) (source R live v o η) z.1)
  have neg:Envelope (fun z:Config G c × Config G n=> -actualAverage R.family (N:=N) (source R live v o η) z.1):=
    ⟨av.meas.neg,av.cost.choose,fun z=>by rw [norm_neg];exact av.cost.choose_spec z⟩
  simpa only [sub_eq_add_neg] using fv.add neg

theorem filed_joint (live:m+1≤N) (ref:R.family.ref 4 ≤ m+1) (v:R.family.label 4) (o:Site n)
    (b q:ℕ) (T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free) (η:ℂ→L[ℝ]ℝ) :
    Measurable (fun z:Config G c × Sample T B G=>filed R live v o b q T B η z.1 z.2) := by
  have toState:Measurable (fun z:Config G c × Sample T B G=>(z.1,state T B z.2)):=
    measurable_fst.prodMk ((measurable_state (G:=G) T B).comp measurable_snd)
  have ef:=WilsonRegisteredPreviousObservable.original R live ref v o b η
  have part:Measurable (fun z:Sample T B G=>η (WilsonRegisteredFrozenReading.previous R live v o b (state T B z))-
      WilsonRegisteredFrozenReading.reading R live v o b q T B η z):=
    (ef.1.meas.comp (measurable_state T B)).sub (WilsonRegisteredFrozenReading.measured R live v o b q T B η ref)
  exact ((centered_joint R live ref v o η).meas.comp toState).sub ((part.const_mul _).comp measurable_snd)

end YM.Integration.WilsonRegisteredHeldMoment
end
