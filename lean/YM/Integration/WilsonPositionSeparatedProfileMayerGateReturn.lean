import YM.Integration.WilsonPositionSeparatedProfileMayerGateSafety
import YM.Integration.WilsonPhysicalHistoryRetainedThermal

/-! Removing the new marked cutoffs from the true zero-decoration moment at
flat boundary charges the one actual Gaussian exceptional set. Every old
signed marked factor stays in the same integral. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open Blaze.March PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt RGLocalTaylor RGLocalTaylor.Insert
open RG01.Survive PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open PhysicalNext.Repeat.Legato
variable {G:Gauge} {c f L:Side} {S:StepData c f} {T:Tube G S} {F:Forest S.ratio} {R:Rep G f}
    {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W s μ C:ℝ} {o:Target.Order G W}
    {H:Cash W s μ L Q o C T R} {j n l k M:ℕ} {χ:Chi}

open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences LocalTaylorR2.Exponent
open WilsonPositionSeparatedProfileMayerMasks WilsonPositionSeparatedProfileMayerGateSafety
open private shared_measure from YM.Integration.WilsonPhysicalHistoryRetainedThermal
variable {run:Run G} {I:Type} [Fintype I] (entry:Submitted run R I) (old:Team R)

def bank := (∏m∈old.own,m.weight)*∏i,WilsonCoherentMayerEntry.wallet run (entry.label i) R.p.threshold (entry.phase i)

def source (a:ℝ) (X:Coat T F) (z:momentSpace X):ℝ:=
  (∏m∈old.own,m.ingredient (field R X z)*anchor R a m.turn X z)*
    ∏i,WilsonCoherentMayerEntry.raw run (entry.label i) (entry.site i) R.p.threshold (entry.phase i) (field R X z)

theorem bound (a:ℝ) (X:Coat T F) (z:momentSpace X) : ‖source entry old a X z‖≤bank entry old:=by
  unfold source bank
  simp only [norm_mul,norm_prod]
  apply mul_le_mul _ _ (Finset.prod_nonneg (fun _ _=>norm_nonneg _)) (Finset.prod_nonneg (fun m _=>m.profit))
  · apply Finset.prod_le_prod
    · intro m _; positivity
    intro m _
    have h:0≤anchor R a m.turn X z ∧ anchor R a m.turn X z≤1:= (X.wrapY z.1).conserve _ _ _
    have hnorm:‖anchor R a m.turn X z‖≤1:=by rw [Real.norm_eq_abs,abs_of_nonneg h.1];exact h.2
    exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans ((mul_one _).le.trans (m.earn _))
  exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>WilsonCoherentMayerEntry.bill run _ _ _ _ _)

private theorem inputs (fund:P.Funds S T) (a:ℝ) (X:Coat T F) (flat:X.blank=X) :
    Measurable (field R X) ∧ (∀m:Wing,Measurable (anchor R a m X)):=by
  let t:momentSpace X→Directions G f:=fun z=>gStep R.beta • X.atmos z.2
  have mt:Measurable t:=by
    apply measurable_pi_lambda;intro e
    exact measurable_const.smul ((X.tale e).measurable.comp measurable_snd)
  have mU:Measurable (fun z:momentSpace X=>X.input (t z)):= X.summon (Y:=fun _=>X.Y) measurable_const mt
  constructor
  · convert mU using 1
    funext z
    exact (WilsonPositionSeparatedProfileMayerFlat.fields (R:=R) fund X flat z.1 z.2 a (.logKey 0)).1
  intro m
  convert ((X.enforce_b (2*a) (X.plaza (areas R T 0 X.B (m.badge S)))).comp mt) using 1
  funext z
  exact (WilsonPositionSeparatedProfileMayerFlat.fields (R:=R) fund X flat z.1 z.2 a m).2

private theorem measurable (fund:P.Funds S T) (a:ℝ) (X:Coat T F) (flat:X.blank=X) :
    Measurable (source entry old a X) ∧ Measurable (fun z=>∏i,gates entry i a X z):=by
  obtain ⟨mf,ma⟩:=inputs (R:=R) fund a X flat
  constructor
  · unfold source
    apply Measurable.mul (Finset.measurable_fun_prod _ (fun m _=>(m.borel.comp mf).mul (ma _)))
    apply Finset.measurable_fun_prod;intro i _
    exact (((entry.phase i).continuous.comp ((run.family.localSection (entry.grade i)).continuous_places _ (entry.site i))).measurable).comp mf
  apply Finset.measurable_fun_prod;intro i _
  apply Measurable.ite _ (ma _) measurable_const
  exact (RG.healthy_closed R.p.threshold (R.activities.reg (entry.key i)).support).measurableSet.preimage mf

private theorem layers (a:ℝ) (X:Coat T F) (z:momentSpace X) : (∏i,gates entry i a X z)∈Set.Icc 0 1:=
  ⟨Finset.prod_nonneg (fun i _=>(priced entry i a X z).1),Finset.prod_le_one (fun i _=>(priced entry i a X z).1) (fun i _=>(priced entry i a X z).2)⟩

theorem original (X:Coat T F) (H:Cash W X.x μ L Q o C T R) (fitted:X.width=o.K) (manifest:X.manifest) (flat:X.blank=X) (stamped:Stamp T) :
    |(∫z,source entry old o.a X z*(∏i,gates entry i o.a X z) ∂Insert.moment X)-
       ∫z,source entry old o.a X z ∂Insert.moment X|≤
    X.dice.real (eerie X (sites entry T X.x) o.ξ R.beta)*bank entry old:=by
  let D:=eerie X (sites entry T X.x) o.ξ R.beta
  let B:=bank entry old
  let v:=source entry old o.a X
  let g:=fun z:momentSpace X=>∏i,gates entry i o.a X z
  have hb:0≤B:=(norm_nonneg (v (1,0))).trans (bound entry old o.a X (1,0))
  have law:=measurable entry old H.laws.data.funds.funds o.a X flat
  have bv:Integrable v (Insert.moment X):=(integrable_const B).mono' law.1.aestronglyMeasurable (ae_of_all _ (bound entry old o.a X))
  have bg:Integrable (fun z=>v z*g z) (Insert.moment X):=by
    apply (integrable_const B).mono' (law.1.mul law.2).aestronglyMeasurable
    filter_upwards with z
    have hg:=layers entry o.a X z
    change ‖v z*g z‖≤B
    have hg1:‖g z‖≤1:=by rw [Real.norm_eq_abs,abs_of_nonneg (show 0≤g z from hg.1)];exact hg.2
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hg1 (norm_nonneg _)).trans ((mul_one _).le.trans (bound entry old o.a X z))
  have hm:MeasurableSet D:=measurable_eerie ..
  have mh:MeasurableSet ((@Prod.snd (F.Slice G) (Air f G)) ⁻¹' D):=hm.preimage measurable_snd
  let bad:=(@Prod.snd (F.Slice G) (Air f G)) ⁻¹' D
  change ‖(∫z,v z*g z ∂Insert.moment X)-(∫z,v z ∂Insert.moment X)‖≤_
  rw [←integral_sub bg bv]
  calc
    _ ≤ ∫z,bad.indicator (fun _=>B) z ∂Insert.moment X:=by
      apply norm_integral_le_of_norm_le ((integrable_const B).indicator mh)
      filter_upwards with z
      by_cases hit:z∈bad
      · rw [Set.indicator_of_mem hit,←mul_sub_one,norm_mul]
        have hg:=layers entry o.a X z
        have diff:‖g z-1‖≤1:=by rw [Real.norm_eq_abs];exact abs_le.mpr ⟨by linarith [show 0≤g z from hg.1],by linarith [show g z≤1 from hg.2]⟩
        exact (mul_le_mul_of_nonneg_left diff (norm_nonneg _)).trans ((mul_one _).le.trans (bound entry old o.a X z))
      · rw [Set.indicator_of_notMem hit]
        have all:g z=1:=Finset.prod_eq_one fun i _=>clear entry X H fitted manifest flat stamped z.1 z.2 hit i
        rw [all,mul_one,sub_self,norm_zero]
    _ = X.dice.real D*B:=shared_measure X D hm B

end YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn
