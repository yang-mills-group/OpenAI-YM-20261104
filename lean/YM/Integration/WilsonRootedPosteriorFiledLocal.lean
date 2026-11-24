import YM.Integration.WilsonRootedPosteriorComparison
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalFiled
import YM.Integration.WilsonRootedNonflatPreviousCost

/-! The signed full previous kinetic and independent spring occurrence
tested against the original and filed local Gibbs laws on one protected
support, with both complete singleton means changed on that support. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPosteriorFiledLocal
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
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type}[DecidableEq I]{Γ:Census I}(R:Run G)
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

def Earned (r:ℕ)(Z:SeriesA G)(σ C ε:ℝ):Prop:=
  ∃f:Γ.Mode→ℝ,(∀i,0≤f i) ∧
    ∀(S:Support fine)(exterior:Config G fine)(W:Config G coarse)(o:Site fine) (a b:I)(legal:({a,b}:Finset I)∈Γ.choices),
    let ξ:=OriginalMarkedConditionalAction.patch S exterior
    let μ:=reference R d.cutoff d.period d.level S exterior W
    let E:=reading R d.cutoff d.period d.level S exterior W (P)
    let L (u:Config G fine→ℂ):=read μ (fun x=>maskedSpringWeight R (N:=d.cutoff) r Z σ C (ξ x)) (fun x=>u (ξ x))
    let w:=fun U=>(WilsonRootedNonflatPreviousCost.letter R d r Z o U:ℂ)
    let u:=slot R d (Πₛ)
    E 1=1 ∧ L 1=1 ∧
    ‖value E w (u (Γ.fire a)) (u (Γ.fire b)) (u ⟨{a,b},legal⟩)-
      value L w (u (Γ.fire a)) (u (Γ.fire b)) (u ⟨{a,b},legal⟩)‖≤
      (ε*S.card*g^2)*WilsonRootedNonflatPreviousCost.bill R d r Z C*(3*f ⟨{a,b},legal⟩+10*f (Γ.fire a)*f (Γ.fire b))

theorem spent (r:ℕ)(Z:SeriesA G){σ C ε:ℝ}(hs:0<σ)(draw:Draw Z σ C)
    (received:LocalSpringRead R d.level d.cutoff d.period r Z σ C ε):
    Earned R d F test r Z σ C ε:=by
  obtain ⟨f,pos,money⟩:=WilsonRootedNonflatIncome.issued R d F test
  have fl:=ManuscriptQLocalActualLog.floor R d F test
  refine ⟨f,pos,?_⟩
  intro S exterior W o a b legal ξ μ E L w u
  obtain ⟨one,uno,gross⟩:=received S exterior W
  have filed:WilsonRootedPosteriorComparison.Filed E L (ε*S.card*g^2):=by
    intro h hm Y yp cy
    obtain ⟨e,l,rate⟩:=gross h Y cy
    exact ⟨yp,e,l,(norm_sub_rev (E h) (L h)) ▸ rate hm⟩
  have path:=WilsonRootedNonflatPreviousCost.invoice R d r Z hs draw o
  have cy(i:Γ.Mode)(U:Config G fine):‖u i U‖≤f i:=by
    change ‖Actual.atMark i (Πₛ) U/((P).eval U:ℂ)‖≤f i
    have h:=(Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below).positive U
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos h,div_le_iff₀ h]
    exact money i U
  have my(i:Γ.Mode):Measurable (u i):=(WilsonRootedPosteriorDifferences.admissible R d _ (fl.safe i)).meas
  have cost (U:Config G fine):‖w U‖≤WilsonRootedNonflatPreviousCost.bill R d r Z C:=by
    change ‖(WilsonRootedNonflatPreviousCost.letter R d r Z o U:ℂ)‖≤_
    rw [Complex.norm_real];exact path.2.2 U
  exact ⟨one,uno,WilsonRootedPosteriorComparison.original E L filed w _ _ _ path.1.ofReal_env.meas
    (my _) (my _) (my _) ((norm_nonneg _).trans (cost 1)) (pos _) (pos _) (pos _) cost (cy _) (cy _) (cy _)⟩
end received

theorem original [Fintype I](simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)(income:WilsonVacuumPreResetPrecursorReserve.Issued R.kit)
    (time:RG01Estimate.Chart.Barrier R.alloy (fun _ i=>((i:ℝ)+1)⁻¹))(credit:Credit)(r cap:ℕ){ε:ℝ}(ep:0<ε):
    ∀ᶠm:ℕ in atTop,∀d:LocalFormal.Datum R.family Γ,d.level=m→d.level+1<d.cutoff→
      let C:=credit.buy (zz (V₀) (d.level+1))+zz (V₀) (d.level+1)*(V₀).clock.loopCap (d.level+1)
      ∀σ Z,0<σ→σ⁻¹≤zz (V₀) (d.level+1)→Draw Z σ C→(∀a∈Z,3≤a.grade ∧ a.grade≤cap)→Z.length ≤ meterPre cap→
      ∀{J:Request I}{A:NumericSchedule R.family J}(F:AnalyticInput J A d)(t:TestSpace J.tests),Earned R d F t r Z σ C ε:=by
  filter_upwards [cofinal_spring_read R simple v rows render income time credit r cap ep] with m payment
  intro d hm live C σ Z hs width draw grades size J A F t
  subst m
  exact spent R d F t r Z hs draw (payment d.cutoff live d.period σ Z hs width draw grades size)
end YM.Integration.WilsonRootedPosteriorFiledLocal
