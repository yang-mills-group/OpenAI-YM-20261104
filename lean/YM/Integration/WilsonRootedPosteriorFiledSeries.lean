import YM.Integration.WilsonRootedPosteriorFiledPrices
import YM.Integration.WilsonRootedPosteriorPositiveSeries
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalRatio

/-! One positive finite vacuum denominator for every true marked moment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorFiledSeries
open Filter Function Finset Lattice RG Wilson Stationary MeasureTheory OPE.Therm
open RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure Pressure.Testing
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonLimitConstruction Pert.Asymptotics OriginalMarkedRunAction
open Progress.DirectedRecipe OriginalMarkedRowCovariance WilsonHeldRetainedAction OriginalMarkedConditionalAction
open WilsonRootedPosteriorObserved (slot)
open WilsonRootedPosteriorComparison (value)
open WilsonRootedPosteriorLocalTangent (linear)
open scoped Topology BigOperators Classical
variable {G:Gauge}

theorem partialPrice (R:Run G){m N per r:ℕ}(live:m+1≤N){Z:SeriesA G}{σ C ε:ℝ}(ep:0≤ε)
    (readable:LocalSpringRead R m N per r Z σ C ε)(osc:LocalSpringOscillation R m N per r Z σ C ε)
    (S:Support (R.family.side (m+1) per))(ext:Config G (R.family.side (m+1) per))(W:Config G (R.family.side m per)):
    let δ:=ε*S.card*(regulatorRun R.family N per (m+1))^2
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R N per m S ext W
    let ν:=springLocalPrior R m N per S ext W
    let h:=springLocalChange R m N per r Z σ C S ext
    let L (u:Config G (R.family.side (m+1) per)→ℂ):=read μ (fun x=>maskedSpringWeight R (N:=N) r Z σ C (ξ x)) (fun x=>u (ξ x))
    δ≤1/8→∀n:ℕ,0<n→
    let j:=springMomentSum ν h n 1
    let T (u:Config G (R.family.side (m+1) per)→ℂ):=springMomentSum ν h n (fun x=>u (ξ x))/j
    1/2≤‖j‖ ∧ WilsonRootedPosteriorComparison.Filed L T (6*(δ^n*springTaylorCost n)):=by
  intro δ ξ μ ν h L small n pn j T
  have physical:=spring_prior_ratio R live ep osc S ext W small n pn
  letI:IsProbabilityMeasure ν:=(spring_prior_first R live osc S ext W).1
  have hb:=spring_prior_bounds R osc S ext
  have posδ:0≤δ:=by dsimp [δ];positivity
  have denom:(1:ℝ)≤2*Real.exp 2:=by linarith [Real.one_le_exp (show (0:ℝ)≤2 by norm_num)]
  have half(x):|h x|≤1/2:=(hb.2 x).trans ((div_le_self posδ denom).trans (small.trans (by norm_num)))
  refine ⟨physical.2.1,?_⟩
  intro f mf b bp cap
  have localEnv:Envelope (fun U=>f (ξ U)):=⟨mf.comp (measurable_patch S ext),b,fun U=>cap _⟩
  have safe:=localEnv.integrableC ν
  have bound:(∫U,‖f (ξ U)‖ ∂ν)≤b:=by
    simpa only [integral_const,probReal_univ,one_smul] using
      (integral_mono safe.norm (integrable_const b) (fun U=>cap (ξ U)))
  refine ⟨bp,((readable S ext W).2.2 f b cap).2.1,WilsonRootedPosteriorPositiveSeries.bounded ν h hb.1 half n _ safe bp (fun x=>cap (ξ x)),?_⟩
  have fee:0 ≤ springTaylorCost n:=by unfold springTaylorCost;positivity
  exact (physical.2.2 f safe).trans (mul_le_mul_of_nonneg_left bound (mul_nonneg (by norm_num) (mul_nonneg (pow_nonneg posδ _) fee)))
variable {I:Type}[DecidableEq I]{Γ:Census I}(R:Run G)
local notation "V₀" => R.family.path.levels
local notation "side" => R.family.side
section received
variable (d:LocalFormal.Datum R.family Γ)[Fintype I]{J:Request I}{A:NumericSchedule R.family J}
    (F:AnalyticInput J A d)(test:TestSpace J.tests)
local notation "g" => regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "Πₛ" => ManuscriptQLocalActualLog.source R d F test
local notation "fine" => side (d.level+1) d.period
local notation "coarse" => side d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)

def Purchased (r:ℕ)(Z:SeriesA G)(σ C ε:ℝ):Prop:=
  ∃f:Γ.Mode→ℝ,(∀i,0≤f i) ∧
    ∀(S:Support fine)(ext:Config G fine)(W:Config G coarse)(o:Site fine)(a b:I)(legal:({a,b}:Finset I)∈Γ.choices),
    let δ:=ε*S.card*g^2
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let μ:=reference R d.cutoff d.period d.level S ext W
    let ν:=springLocalPrior R d.level d.cutoff d.period S ext W
    let h:=springLocalChange R d.level d.cutoff d.period r Z σ C S ext
    let L (u:Config G fine→ℂ):=read μ (fun x=>maskedSpringWeight R (N:=d.cutoff) r Z σ C (ξ x)) (fun x=>u (ξ x))
    let w:=fun U=>(WilsonRootedNonflatPreviousCost.letter R d r Z o U:ℂ)
    let u:=slot R d (Πₛ)
    let A':=Γ.fire a
    let B':=Γ.fire b
    let J':Γ.Mode:=⟨{a,b},legal⟩
    δ≤1/8→∀n:ℕ,0<n→
    let j:=springMomentSum ν h n 1
    let T (f:Config G fine→ℂ):=springMomentSum ν h n (fun x=>f (ξ x))/j
    1/2≤‖j‖ ∧ ‖value L w (u A') (u B') (u J')-value T w (u A') (u B') (u J')‖≤
      6*(δ^n*springTaylorCost n)*WilsonRootedNonflatPreviousCost.bill R d r Z C*(3*f J'+10*f A'*f B')

theorem spent (r:ℕ)(Z:SeriesA G){σ C ε:ℝ}(hs:0<σ)(draw:Draw Z σ C)(ep:0≤ε)
    (readable:LocalSpringRead R d.level d.cutoff d.period r Z σ C ε)
    (osc:LocalSpringOscillation R d.level d.cutoff d.period r Z σ C ε):
    Purchased R d F test r Z σ C ε:=by
  obtain ⟨f,pos,money⟩:=WilsonRootedNonflatIncome.issued R d F test
  have fl:=ManuscriptQLocalActualLog.floor R d F test
  refine ⟨f,pos,?_⟩
  intro S ext W o a b legal δ ξ μ ν h L w u A' B' J' small n pn j T
  have quote:=partialPrice R d.below ep readable osc S ext W small n pn
  refine ⟨quote.1,?_⟩
  have path:=WilsonRootedNonflatPreviousCost.invoice R d r Z hs draw o
  have cy(i:Γ.Mode)(U:Config G fine):‖u i U‖≤f i:=by
    change ‖Actual.atMark i (Πₛ) U/((P).eval U:ℂ)‖≤f i
    have good:=(Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below).positive U
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos good,div_le_iff₀ good]
    exact money i U
  have my(i:Γ.Mode):Measurable (u i):=(WilsonRootedPosteriorDifferences.admissible R d _ (fl.safe i)).meas
  have cost(U:Config G fine):‖w U‖≤WilsonRootedNonflatPreviousCost.bill R d r Z C:=by
    change ‖(WilsonRootedNonflatPreviousCost.letter R d r Z o U:ℂ)‖≤_
    rw [Complex.norm_real];exact path.2.2 U
  exact WilsonRootedPosteriorComparison.original L T quote.2 w (u A') (u B') (u J') path.1.ofReal_env.meas
    (my _) (my _) (my _) ((norm_nonneg _).trans (cost 1)) (pos _) (pos _) (pos _) cost (cy _) (cy _) (cy _)
end received

theorem original [Fintype I](simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)(income:WilsonVacuumPreResetPrecursorReserve.Issued R.kit)
    (time:RG01Estimate.Chart.Barrier R.alloy (fun _ i=>((i:ℝ)+1)⁻¹))(credit:Credit)(r cap:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠm:ℕ in atTop,∀d:LocalFormal.Datum R.family Γ,d.level=m→d.level+1<d.cutoff→
      let C:=credit.buy (zz (V₀) (d.level+1))+zz (V₀) (d.level+1)*(V₀).clock.loopCap (d.level+1)
      ∀σ Z,0<σ→σ⁻¹≤zz (V₀) (d.level+1)→Draw Z σ C→(∀a∈Z,3≤a.grade ∧ a.grade≤cap)→Z.length ≤ meterPre cap→
      ∀{J:Request I}{A:NumericSchedule R.family J}(F:AnalyticInput J A d)(t:TestSpace J.tests),Purchased R d F t r Z σ C ε:=by
  filter_upwards [cofinal_spring_read R simple v rows render income time credit r cap ep,
    cofinal_spring_oscillation R simple v rows render income time credit r cap ep] with m money earned
  intro d hm live C σ Z hs width draw grades size J A F t
  subst m
  exact spent R d F t r Z hs draw ep.le (money d.cutoff live d.period σ Z hs width draw grades size)
    (earned d.cutoff live d.period σ Z hs width draw grades size)
end YM.Integration.WilsonRootedPosteriorFiledSeries
