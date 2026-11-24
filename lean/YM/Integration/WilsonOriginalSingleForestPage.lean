import YM.Integration.WilsonOriginalJointForestRay
import YM.Integration.WilsonOriginalSingleGaussianDivision

/-! A funded finite block with one selected incoming marker, permitting independently
signed actual radial polynomials for every original coefficient in that marker. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSingleForestPage
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series Series.Radial Series.Tested
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos Next.Rank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative credit)
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  {V:Type}[DecidableEq V][Fintype V]{C:Marker.Census V}(Y:Bulk.Colors C G (fine R i per))
local notation "S" => step R i per
local notation "K" => model R N i per hi
local notation "φ" => relative R N i per hi F (covered R N i per)

open PhysicalForestMarkedRay WilsonOriginalEarnedUnaryDriver
open WilsonOriginalJointForestRay (forward Rays)
open WilsonOriginalSingleGaussianReceipt
variable (B:fieldDir G (coarse R i per) 1)(o:Hot C){A:Type}[Fintype A]
    (a:A→ℂ)(U:A→Ink (Woods G (fine R i per)))(r:ℕ)
local notation "placed" => forward R N i per hi F
local notation "q₀" => ((model R N i per hi).covariance F tag)

def Single :Prop:=∀(s:Hot C)(j:ℕ),j≤r → ∀z:Precision.Key F G→ℝ,
  readJet (Y.power s+j) (chartMark S F (saddle R N i per F) K B z Y s)=
    (if s.val=o.val then ∑d,a d*(MvPolynomial.eval (Sum.elim z (flatten B)) (coeff j (placed (U d))):ℝ) else 0)

private theorem centered {T:Type}[CommRing T](P:PowerSeries T):
    constantCoeff (P-PowerSeries.C (constantCoeff P))=0:=by simp

def recorded (e:ℕ)(Z:SeriesA G)(well:Bulk.Well Y)(paid:Single R N i per hi F Y B o a U r):
    Page (Precision.Key F G) (Woods G (coarse R i per)) A C r where
  B:=flatten B
  source:=o.val
  live:=o.prop
  phase:=φ
  zero:=centered _
  mark d:=placed (U d)
  amplitude:=a
  driver:=driver R N i per hi F tag Y B e Z r
  written:=by
    let empty : Empty→Ink (Woods G (fine R i per)):=Empty.elim
    let zero : Empty→ℂ:=Empty.elim
    have joint:Rays R N i per hi F Y B o o a zero U empty r:=by
      intro s j h z
      simpa using paid s j h z
    intro s z
    have h:=WilsonOriginalJointForestRay.written R N i per hi F tag Y B o o a zero U empty r e Z well joint s z
    simpa [WilsonOriginalJointGaussianAdmission.source,WilsonOriginalJointGaussianIncome.income,
      WilsonOriginalSingleGaussianPass.deposit] using h

theorem original {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}(well:Bulk.Well Y)
    (bank:Issued R N (i+1) e (Z (i+1)) σ cash)(B₀:Stationary.Link G (coarse R i per))(hr:r≤e+2)
    (paid:Single R N i per hi F Y (Stationary.arm G (coarse R i per) 1 B₀) o a U r):
    let held:=Stationary.arm G (coarse R i per) 1 B₀
    let W:=recorded R N i per hi F tag Y held o a U r e (Z (i+1)) well paid
    let actual:=Bulk.Fk K F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) Y) held r
    let output:=WilsonOriginalSingleMarkedRegister.token C r o.val * WilsonOriginalSingleGaussianDivision.row W q₀
    Comparison.RG02.Order.ratio actual=1+output ∧ Order.logMarked actual=output:=by
  intro held W actual output
  have h:=WilsonOriginalEarnedUnaryDriver.original R N i per hi F tag Y course lo well bank B₀ r hr
  exact ⟨h.1.trans (WilsonOriginalSingleGaussianDivision.normalized W q₀ ((K).symm F tag)),
    h.2.trans (WilsonOriginalSingleGaussianDivision.logarithm W q₀ ((K).symm F tag))⟩

end YM.Integration.WilsonOriginalSingleForestPage
