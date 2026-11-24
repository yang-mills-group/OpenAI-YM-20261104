import YM.Integration.WilsonOriginalProjectedCurvatureAdmission
import YM.Integration.WilsonMatrixTicketLanesSelectedNormalization

/-! The registered whole Q row at its independently nominated reporting clock.
The upper regulator is allowed to move after the reporting date is fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureReportingClock
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope WilsonOriginalProjectedCurvatureCredits
open private date from YM.Integration.WilsonReportingMeasuredWardFunding
open FullQLocal FullQLocal.RenderedStep
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) (hg:G.Simple) {B:MS.Local.Physical.Deck G}
  {V:Type} [DecidableEq V] [Fintype V] (J:Request V) (Q:MS.Land.Prescription B)
  (u:V→MS.Rake.Label B) (μ σ:ℝ) (extra:V→ℕ) (w:V→ℝ)

local notation "asked" => WilsonOriginalProjectedCurvatureClock.charge R J u σ σ extra w
local notation "β̂" => R.family.path.levels.clock.hatBeta

include hg
theorem original (K:ℕ) (hw:∀j,0<w j) :
    ∃ C:ℝ,1≤C ∧ ∃ b:ℕ,∀ j (Ω:ℝ),0<Ω →
      ∀ (N p L:ℕ) (o:V→Site (R.family.side L p)) (orders:V→ℕ),
      (∀i,orders i≤K) → L≤N → 0<Pert.Asymptotics.regulatorRun R.family N p L →
      Pert.Asymptotics.regulatorRun R.family N p L≤1 →
      let D:=ActualOriginalQPointSetup.pointDatum R J p L o
      let η:=(μ+R.family.S.scale N-R.family.S.scale j)-R.family.S.scale N
      let X:=WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
      let a:=C*(β̂ j)^b
      (∀i,0<w i/(a*Ω)) ∧ QuadraticLocal.Earn.Offers X (fun i=>w i/(a*Ω)) σ Ω⁻¹ ∧
        ∀ k:(Stock.census V).Mode,Poly.toll (fun i=>w i/(a*Ω)) k*(a*Ω)^k.val.card=Poly.toll w k := by
  obtain ⟨c,hc,b,h⟩:=WilsonOriginalProjectedCurvatureClock.quoted R J Q u μ σ σ extra w K hw
  obtain ⟨A,hA,at_date⟩:=date R hg
  let C:=max 1 c*(max 1 A)^b*max 1 asked
  have hC:1≤C:=one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left ..) (one_le_pow₀ (le_max_left ..))) (le_max_left ..)
  refine ⟨C,hC,b,?_⟩
  intro j Ω Ωpos N p L o orders capped lower gpos upper D η X a
  have stamp:η=μ-R.family.S.scale j:=by dsimp only [η]; ring
  have βpos:0<β̂ j:=zero_lt_one.trans (R.alloy.B.a.fits.delayed j)
  have apos:0<a:=mul_pos (zero_lt_one.trans_le hC) (pow_pos βpos _)
  have metric:1+‖R.family.S.scale j‖ ≤ max 1 A*(β̂ j):=
    (at_date j).trans (mul_le_mul_of_nonneg_right (le_max_right ..) βpos.le)
  have cash:c*(1+‖R.family.S.scale j‖)^b*asked≤a:=by
    calc
      _ ≤ c*(1+‖R.family.S.scale j‖)^b*max 1 asked:=
        mul_le_mul_of_nonneg_left (le_max_right ..) (mul_nonneg hc.le (pow_nonneg (by positivity) _))
      _ ≤ (max 1 c*(max 1 A*(β̂ j))^b)*max 1 asked:=
        mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right ..)
          (pow_le_pow_left₀ (by positivity) metric b) (pow_nonneg (by positivity) _) (zero_le_one.trans (le_max_left ..)))
          (zero_le_one.trans (le_max_left ..))
      _ = a:=by dsimp only [a,C]; rw [mul_pow]; ring
  have paid:QuadraticLocal.Earn.Offers X w σ a:=by
    intro x
    have paidAt:=WilsonOriginalProjectedCurvatureLamps.offers Q D u η orders N σ σ extra w lower gpos upper hw x
    have same:=WilsonOriginalProjectedCurvaturePointCredit.same R J Q u p L o η orders σ σ extra w
    have native:=h j orders capped
    rw [←stamp] at native
    exact ⟨paidAt.1,paidAt.2.1,paidAt.2.2.trans (same.le.trans (native.trans cash))⟩
  have unit:=WilsonOriginalProjectedCurvatureMarkerIncome.unit Q D u η orders N σ extra w apos le_rfl paid
  have scaled:=WilsonOriginalProjectedCurvatureAdmission.divide Q D u η orders N σ extra (fun k=>w k/a) Ωpos unit
  refine ⟨fun k=>div_pos (hw k) (mul_pos apos Ωpos),?_,
    WilsonOriginalProjectedCurvatureMarkerIncome.recovery w (mul_pos apos Ωpos)⟩
  simpa only [div_div,one_div] using scaled

end YM.Integration.WilsonOriginalProjectedCurvatureReportingClock
