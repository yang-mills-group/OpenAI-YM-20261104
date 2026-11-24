import YM.Integration.WilsonOriginalProjectedCurvatureReportingGeometry
import YM.Integration.WilsonMovingMentorRootRadius

/-! The actual growing, enrolled geometric support exponent costs one measured
inverse-temperature power at the reporting date on every fixed test roster. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureMovingClock
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvatureReportingGeometry
open private date from YM.Integration.WilsonReportingMeasuredWardFunding
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hg:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ:ℝ) (extra:V→ℕ) (w:V→ℝ)
local notation "D₁" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)
local notation "Rows" => ActualOriginalQPackets.Row (R:=R) u
local notation "β̂" => R.family.path.levels.clock.hatBeta
local notation "J₀" => R.alloy.B.a.clock.J
local notation "wallet" => (∑s:Rows,|salary R J u w s|)

include hg
theorem purchased (K:ℕ) (hw:∀i,0<w i) :
    ∃ C:ℝ,1≤C ∧ ∃ b:ℕ,∀ᶠ j:ℕ in Filter.atTop, ∀ (σ Ω:ℝ),0<Ω →
      Real.exp (((J₀ j:ℝ)+1)*|σ|)≤β̂ j →
      ∀ (N p L:ℕ) (o:V→Site (R.family.side L p)) (orders:V→ℕ),
      (∀i,orders i≤K) → L≤N → 0<Pert.Asymptotics.regulatorRun R.family N p L →
      Pert.Asymptotics.regulatorRun R.family N p L≤1 →
      let D:=ActualOriginalQPointSetup.pointDatum R J p L o
      let η:=(μ+R.family.S.scale N-R.family.S.scale j)-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ j)^(b+1)
      (∀i,0<w i/(a*Ω)) ∧ QuadraticLocal.Earn.Offers X (fun i=>w i/(a*Ω)) σ Ω⁻¹ ∧
        ∀ k:(Stock.census V).Mode,Poly.toll (fun i=>w i/(a*Ω)) k*(a*Ω)^k.val.card=Poly.toll w k := by
  obtain ⟨c,hc,b,atoms⟩:=ActualOriginalFeeGrowth.shifted_bound B Q u K μ
  obtain ⟨A,hA,at_date⟩:=date R hg
  let C:=max 1 c*(max 1 A)^b*max 1 wallet
  have hC:1≤C:=one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left ..) (one_le_pow₀ (le_max_left ..))) (le_max_left ..)
  refine ⟨C,hC,b,?_⟩
  filter_upwards [WilsonOriginalProjectedCurvatureReportingGeometry.eventual R J u extra] with j large
  intro σ Ω hΩ early N p L o orders cap lower gpos upper D η X a
  let ask:=WilsonOriginalProjectedCurvatureClock.charge R J u σ σ extra w
  have βpos:0<β̂ j:=zero_lt_one.trans (R.alloy.B.a.fits.delayed j)
  have apos:0<a:=mul_pos (zero_lt_one.trans_le hC) (pow_pos βpos _)
  have stamp:η=μ-R.family.S.scale j:=by dsimp only [η]; ring
  have native:invoice Q D₁ u η orders σ σ extra w ≤ c*(1+‖R.family.S.scale j‖)^b*ask:=by
    rw [stamp]
    dsimp only [ask,WilsonOriginalProjectedCurvatureClock.charge]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    unfold WilsonOriginalProjectedCurvatureCredits.quoted
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (atoms s.1.1 (orders s.1.1) (cap _) s.1.2 (R.family.S.scale j))
      (mul_nonneg (ActualOriginalQCharges.row_price_nonneg D₁ u w (σ+σ) hw s) (Real.exp_pos _).le)
  have geometry:ask ≤ max 1 wallet*(β̂ j):=(bought R J u extra w large early).trans
    (mul_le_mul_of_nonneg_right (le_max_right ..) βpos.le)
  have metric:1+‖R.family.S.scale j‖ ≤ max 1 A*(β̂ j):=
    (at_date j).trans (mul_le_mul_of_nonneg_right (le_max_right ..) βpos.le)
  have cash:c*(1+‖R.family.S.scale j‖)^b*ask≤a:=calc
    _ ≤ c*(1+‖R.family.S.scale j‖)^b*(max 1 wallet*(β̂ j)):=
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

end YM.Integration.WilsonOriginalProjectedCurvatureMovingClock
