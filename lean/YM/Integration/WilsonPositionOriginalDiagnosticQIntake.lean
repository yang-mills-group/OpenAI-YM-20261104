import YM.Integration.WilsonOriginalFreshQAtReceivedDate

/-! Fund the complete original Q source at the moving MS scale, including
the uncut and masked modes, the old tests, and the actual regular and
compulsory allowances. All reference dates through the birth are admitted
after a single fixed threshold on the elected course. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticQIntake
open Function Filter Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvatureReportingGeometry
open private date from YM.Integration.WilsonReportingMeasuredWardFunding
open scoped Classical BigOperators
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor QuadraticLocal.MintClock
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit AllOrder.Transit.WheelP
open Push.PriceCompiler Org ConnectedActivityE6
open LocalComparison ComparisonDensity.Address Comparison.Density.RenderM MergeProof.Accent FVA1
open FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureLamps
open WilsonOriginalFreshQWallet
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (hg:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
local notation "D₁" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "β̂" => R.family.path.levels.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "wallet" => (∑s:Rows,|salary R J u w s|)


/-- Read the actual elected purchase at one named date with specified
constants. This keeps its original marked tests and both hard accounts. -/
abbrev Dated {A : ℝ → ℕ → ℕ → Prop}
    (_purchase : ∃ C : ℝ, 1≤C ∧ ∃ b : ℕ, ∀ᶠ j : ℕ in atTop, A C b j)
    (C : ℝ) (b j : ℕ) := A C b j

include hg in
theorem charged (K : ℕ) (hw : ∀i,0<w i) :
    ∃ C:ℝ, 1≤C ∧ ∃ b:ℕ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ j,
      Dated (WilsonOriginalProjectedCurvatureMovingClock.purchased
        R hg J Q u (μ+R.family.S.scale m) extra w K hw) C b j := by
  obtain ⟨c,hc,b,atoms⟩:=ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  obtain ⟨A,hA,at_date⟩:=date R hg
  let C:=max 1 c*(max 1 A)^b*max 1 wallet
  have hC:1≤C:=one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left ..) (one_le_pow₀ (le_max_left ..))) (le_max_left ..)
  refine ⟨C,hC,b,?_⟩
  filter_upwards [WilsonOriginalProjectedCurvatureReportingGeometry.eventual R J u extra] with j large
  intro m hm σ Ω hΩ early N p L o orders cap lower gpos upper D η X a
  let ask:=WilsonOriginalProjectedCurvatureClock.charge R J u σ σ extra w
  have βpos:0<β̂ j:=zero_lt_one.trans (R.alloy.B.a.fits.delayed j)
  have apos:0<a:=mul_pos (zero_lt_one.trans_le hC) (pow_pos βpos _)
  let δ := R.family.S.scale j - R.family.S.scale m
  have stamp : η = μ-δ := by dsimp only [δ,η]; ring
  have lowerScale : 0 ≤ R.family.S.scale m := by
    simpa using (OPE.scale_mono R.family.S).monotone (Nat.zero_le m)
  have ordered := (OPE.scale_mono R.family.S).monotone hm
  have gap : ‖δ‖ ≤ ‖R.family.S.scale j‖ := by
    simp only [δ, Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ordered),
      abs_of_nonneg (lowerScale.trans ordered)]
    linarith
  have native:invoice Q D₁ u η orders σ σ extra w ≤ c*(1+‖δ‖)^b*ask:=by
    rw [stamp]
    dsimp only [ask,WilsonOriginalProjectedCurvatureClock.charge]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    unfold WilsonOriginalProjectedCurvatureCredits.quoted
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (atoms s.1.1 (orders s.1.1) (cap _) s.1.2 δ)
      (mul_nonneg (ActualOriginalQCharges.row_price_nonneg D₁ u w (σ+σ) hw s) (Real.exp_pos _).le)
  have geometry:ask ≤ max 1 wallet*(β̂ j):=(bought R J u extra w large early).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) βpos.le)
  have metric:1+‖δ‖ ≤ max 1 A*(β̂ j):=
    (add_le_add_right gap 1).trans ((at_date j).trans (mul_le_mul_of_nonneg_right (le_max_right ..) βpos.le))
  have cash:c*(1+‖δ‖)^b*ask≤a:=calc
    _ ≤ c*(1+‖δ‖)^b*(max 1 wallet*(β̂ j)):=
      mul_le_mul_of_nonneg_left geometry (mul_nonneg hc.le (pow_nonneg (by positivity) _))
    _ ≤ (max 1 c*(max 1 A*(β̂ j))^b)*(max 1 wallet*(β̂ j)):=
      mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right ..)
        (pow_le_pow_left₀ (by positivity) metric b) (pow_nonneg (by positivity) _) (zero_le_one.trans (le_max_left ..)))
        (mul_nonneg (zero_le_one.trans (le_max_left ..)) βpos.le)
    _ = a:=by dsimp only [a,C]; rw [mul_pow,pow_succ]; ring
  have paid:QuadraticLocal.Earn.Offers X w σ a:=by
    intro x
    have root:=WilsonOriginalProjectedCurvatureLamps.offers Q D u η orders N σ σ extra w lower gpos upper hw x
    have same:=WilsonOriginalProjectedCurvaturePointCredit.same R J Q u p L o η orders σ σ extra w
    exact ⟨root.1,root.2.1,root.2.2.trans (same.le.trans (native.trans cash))⟩
  have unit:=WilsonOriginalProjectedCurvatureMarkerIncome.unit Q D u η orders N σ extra w apos le_rfl paid
  have scaled:=WilsonOriginalProjectedCurvatureAdmission.divide Q D u η orders N σ extra (fun k=>w k/a) hΩ unit
  refine ⟨fun k=>div_pos (hw k) (mul_pos apos hΩ),?_,
    WilsonOriginalProjectedCurvatureMarkerIncome.recovery w (mul_pos apos hΩ)⟩
  simpa only [div_div,one_div] using scaled

variable {ψ : ℕ → ℕ} (root : PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (income : WilsonMovingMentorRootRadius.Income (M:=R.metals) root ψ R.alloy.delay)
  (warm : Spill.Raffle.Warm G root R.alloy.delay ψ)
local notation "h" => Fintype.card V
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u
local notation "v" => h*t
local notation "rank" => ActualOriginalQLayout.rankCap R u
local notation "head" => (rank+v+1)
local notation "βE" => R.alloy.B.a.clock.hatBeta
local notation "stage" => R.alloy.B.a.clock.J


include hg income warm in
theorem purchased (order : ℕ) (positive : ∀ i, 0 < w i) :
    ∃ C : ℝ, 1≤C ∧ ∃ b : ℕ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ j,
      Dated (WilsonOriginalFreshQAtReceivedDate.prepaid R hg J Q u
        (μ+R.family.S.scale m) extra w root income warm order positive) C b j := by
  obtain ⟨C,hC,b,source⟩ := charged R hg J Q u μ extra w order positive
  refine ⟨C,hC,b,?_⟩
  have deep := R.alloy.B.a.fits.deep.eventually_ge_atTop (rank + v + h)
  filter_upwards [source,deep] with m filed grades
  intro ref href k reached Ω hΩ N per o orders bound lo seed π Γ H course start alive
  dsimp only
  intro E _ _ A K oldHome old fresh apart offer pos fits
  let D := ActualOriginalQPointSetup.pointDatum R J per m o
  let η := ((μ+R.family.S.scale ref)+R.family.S.scale N-R.family.S.scale m)-R.family.S.scale N
  let σ := Poetry.Agenda.seed root ψ k (stage m)
  let a := C*(βE m)^(b+1)
  let wQ := fun i => w i/(a*Ω)
  let X := cohort Q D u η orders N σ extra
  let g := Pert.Asymptotics.regulatorRun R.family N per m
  have entry := course.1.walk m start alive
  have glaw : g = Coat.gStep (H m).beta := by rw [entry.beta]; rfl
  have raw := WilsonMovingMentorRaffleCourse.measured R warm course start reached
    (show rank ≤ stage m by omega) (show v ≤ stage m by omega) (show h ≤ stage m by omega) alive
  obtain ⟨rawInvoice,gross⟩ := raw
  rw [←glaw] at rawInvoice
  have wide := WilsonMovingMentorRootRadius.at_date (ψ:=ψ) R root income m k reached
  obtain ⟨sourcePos,charges,restore⟩ := filed ref href σ Ω hΩ wide N per m o orders bound alive rawInvoice.1 rawInvoice.2.1
  have census := WilsonOriginalProjectedCurvatureProduction.census R u
  have book : Scene.Armada X wQ (fun _ => t) σ Ω⁻¹ rank h v :=
    ⟨⟨fun s => (census s).1,fun s => (census s).2⟩,sourcePos,charges,
      WilsonOriginalProjectedCurvatureLamps.issued Q D u η orders N σ extra,
      fun i => (WilsonOriginalProjectedCurvatureRender.priced Q D u η orders N i.1 σ
        (extra i.1.1.1) i.2).1⟩
  have native := WilsonOriginalFreshQWallet.original Q D u η orders N σ extra A K
    oldHome old fresh apart (H m).p alive book pos fits rawInvoice
  have same : Spes.Market.tuning (R.metals.p.profile (stage m)) (H m).p (βE m) := by
    rw [entry.truep.point,←params_eq R.alloy.B.valid m]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  have quote := Spill.Raffle.regular G (R.metals.p.profile (stage m)) σ rank v h (H m).p (βE m)
    same.2.2 same.2.1
  rw [quote] at native
  refine ⟨native,restore,?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right gross (inv_nonneg.mpr hΩ.le)

end YM.Integration.WilsonPositionOriginalDiagnosticQIntake
