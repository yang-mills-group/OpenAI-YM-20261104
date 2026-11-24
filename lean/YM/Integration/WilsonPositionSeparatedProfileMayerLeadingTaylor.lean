import YM.Integration.WilsonPositionSeparatedProfileMayerLeadingWindow
import YM.Integration.WilsonCoherentMayerBorn
import YM.Integration.WilsonCoherentMayerSignedCharge

/-! Taylor expenditure under the complete signed incumbent team, after the
physical safety gates have been discharged on the bounded Wilson fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileMayerLeadingTaylor
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

open Precision Coat Source Matrix Dict06 AnalyticBridge.LocalGaussianLaws ProbabilityTheory
open WilsonCoherentMayerSubmission WilsonCoherentMayerOccurrences
open WilsonPositionSeparatedProfileMayerGateReturn WilsonCoherentMayerHearing
open private inputs measurable from YM.Integration.WilsonPositionSeparatedProfileMayerGateReturn

variable (old:Team R) (a:ℝ) (X:Coat T F)

def prior (z:momentSpace X):ℝ:=∏m∈old.own,m.ingredient (field R X z)*anchor R a m.turn X z

theorem bound (z:momentSpace X):|prior old a X z|≤∏m∈old.own,m.weight:=by
  change ‖prior old a X z‖≤_;unfold prior;rw [norm_prod];apply Finset.prod_le_prod (fun _ _=>norm_nonneg _)
  intro m _;rw [norm_mul]
  have h:0≤anchor R a m.turn X z ∧ anchor R a m.turn X z≤1:=(X.wrapY z.1).conserve _ _ _
  have hnorm:‖anchor R a m.turn X z‖≤1:=by rw [Real.norm_eq_abs,abs_of_nonneg h.1];exact h.2
  exact (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans ((mul_one _).le.trans (m.earn _))

def printed {I:Type} [Fintype I] (run:Run G) (entry:Submitted run R I) (t:ℕ) (z:momentSpace X):ℝ:=
  prior old a X z*WilsonCoherentMayerSignedCharge.polynomial run entry.grade (F:=F) entry.site entry.phase R.p.threshold (Coat.gStep R.beta) entry.label t z.2

theorem original {I:Type} [Fintype I] (run:Run G) (d:I→ℕ) (P:Teller G) (L:Side) (D:Patch) (branch:D.Branches P.bind G) (t:ℕ):
    ∃table:ℝ,0≤table ∧ ∀ᶠ s:ℝ in atTop,∀ {c f:Side} {S:StepData c f} (T:Tube G S) {R:Rep G f} {W μ C:ℝ} {o:Target.Order G W} {Q:ConnectedActivityE6.Target G P}
    (_H:Cash W s μ L Q o C T R) {F:Forest S.ratio} (X:Coat T F),X.x=s→S.patch=D→S.patch.L=L→X.manifest→P.Funds S T→X.blank=X→X.V=1→Assembly.Clear S X.x X.seeds F→0<R.beta→
    ∀entry:Submitted run R I,d=entry.grade→(∀i h,|entry.phase i h|≤‖h‖)→∀old:Team R,
    |(∫z,source entry old o.a X z ∂moment X)-(∫z,printed old o.a X run entry t z ∂moment X)|≤
      (∏m∈old.own,m.weight)*(WilsonCoherentReportingPivot.mass run entry.grade R.p.threshold entry.label*(table*(Coat.gStep R.beta)^(t+1))):=by
  obtain ⟨table,ht,issued⟩:=WilsonCoherentMayerSignedCharge.original run d P L D branch t
  refine ⟨table,ht,?_⟩;filter_upwards [issued] with s spent
  intro c f S T R W μ C o Q H F X hx dp dl hm fund flat hv clear hot entry same phase old
  subst d
  have read:=inputs (R:=R) fund o.a X flat
  have seen:Measurable (prior old o.a X):=by
    apply Finset.measurable_prod;intro m _;exact (m.borel.comp read.1).mul (read.2 m.turn)
  have weight:0≤∏m∈old.own,m.weight:=Finset.prod_nonneg (fun m _=>m.profit)
  have quote:=spent c f S T F X hx dp dl H.laws.data.room hm fund hv clear entry.site entry.phase phase R.p.threshold R.beta (Coat.gStep R.beta) hot (inv_pos.mpr (Real.sqrt_pos.mpr hot)) entry.label (prior old o.a X) weight seen (bound old o.a X)
  let stock:=source entry old o.a X
  let ink:=printed old o.a X run entry t
  have eqn:(fun z=>prior old o.a X z*WilsonCoherentMayerSignedCharge.residual run entry.grade entry.site X entry.phase R.p.threshold R.beta (Coat.gStep R.beta) entry.label t z)=(fun z=>stock z-ink z):=by
    funext z
    have sampled:=WilsonCoherentMayerBorn.sample (H:=H) entry X hx hm hot z
    rw [WilsonCoherentMayerSubmission.full] at sampled
    simp only [stock,ink,source,printed,WilsonCoherentMayerSignedCharge.residual,prior]
    change _ = _*(∏i,entry.phase i (Push.Local.presented (run.family.localSection (entry.grade i)) (entry.site i) R.p.threshold (entry.label i) (field R X z)))-_
    rw [sampled];ring
  change Integrable _ (moment X) ∧ _ at quote
  rw [eqn] at quote
  have bm:=measurable entry old fund o.a X flat
  have real:Integrable stock (moment X):=Integrable.of_bound bm.1.aestronglyMeasurable (bank entry old) (ae_of_all _ (WilsonPositionSeparatedProfileMayerGateReturn.bound entry old o.a X))
  have drawn:Integrable ink (moment X):=by simpa only [Pi.sub_def,sub_sub_cancel] using real.sub quote.1
  rw [←integral_sub real drawn]
  change ‖∫z,stock z-ink z ∂moment X‖≤_
  exact (norm_integral_le_integral_norm (μ:=moment X) (fun z=>stock z-ink z)).trans (by simpa only [Real.norm_eq_abs] using quote.2)

end YM.Integration.WilsonPositionSeparatedProfileMayerLeadingTaylor
