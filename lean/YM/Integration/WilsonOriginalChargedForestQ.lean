import YM.Integration.WilsonOriginalBoughtForestQ
import YM.Integration.SignedOpeningPathFamily

/-! The original registered Q at any admitted date, in its independently registered signed path presentation on the actual occupied forest. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalChargedForestQ
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Comparison.Density.RenderM NativePaidPacketColors MergeProof MergeProof.Accent
open PertExtension Series Series.Radial Series.Tested RegulatorIR RegulatorIR.FVAAlt2
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Power WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open ActualRunCalibrationTests OriginalSourceJetAddresses FundedOriginalMarkedInput
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner


open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open Next.SectorChange

variable {G:Gauge}(R:Run G){deck:MS.Local.Physical.Deck G}(N i per:ℕ)(hi:i < N)
  {n:ℕ}{hn:n ≤ i + 1}{V:Type}[DecidableEq V][Fintype V]
  (Q:MS.Land.Prescription deck)(D:ActualRunQlocalNativeTuple.Datum R per (i + 1) n hn V)
  (u:V→MS.Rake.Label deck)(μ:ℝ)(orders:V→ℕ)(scale:V→ℂ) (x:TestSpace (ActualRunQlocalNativeTuple.orbit D))
local notation "C" => Stock.census V
local notation "P" => ActualOriginalQFrozenInput.packets Q D u μ orders N
local notation "v₀" => (Bulk.Colors.noHole G (R.family.side (i + 1) per) C).vac
local notation "Y" => NativePaidPacketColors.colors P v₀ (fun j=>scale j • x j)
local notation "S" => step R i per
local notation "K" => model R N i per hi

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)
variable (z:Precision.Key F G→ℝ)
local notation "M" => saddle R N i per F

open WilsonOriginalBoughtForestQ

/-- The physical Gaussian free- and fixed-boundary coordinates are the two original affine coordinates. -/
theorem same_axes :
    SignedRegisteredKernelPolynomial.focus F B z = PhysicalForestRay.sample S F B z := by
  change Sum.elim ((vcloth S F G).symm ((vcloth S F G) z))
    ((Stationary.arm G (coarse R i per) 1).symm
      (Stationary.arm G (coarse R i per) 1 (flatten B))) = Sum.elim z (flatten B)
  rw [ContinuousLinearEquiv.symm_apply_apply,ContinuousLinearEquiv.symm_apply_apply]

def registered : PTable C := PowerSeries.mk fun d => lit C fun J =>
  Cloud.paint z (SignedOpeningPathFamily.polynomial Q D u μ orders scale K F M x B d J.val)

/-- All proper subwords use the one before-test path family with their actual deposited positions. -/
theorem filed :
    published R N i per hi Q D u μ orders scale x F B z =
      registered R N i per hi Q D u μ orders scale x F B z := by
  apply PowerSeries.ext
  intro d
  rw [published, registered, coeff_mk, coeff_mk]
  apply congrArg (lit C)
  funext J
  rw [← SignedOpeningPathFamily.charged]
  simp only [_root_.map_sum, _root_.map_smul, smul_eq_mul,SignedRegisteredMarkedProgram.reading]

theorem original {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i)
    (B₀:Stationary.Link G (coarse R i per))(l:ℕ)(hl:l ≤ e + 2)(s:(Board C l).Mode):
    let B:=Stationary.arm G _ 1 B₀
    (Bulk.Fk K F tag (QuadraticLocal.Fk.grant (π (i + 1)) (Step.tape (e + 2)) Y) B l).part s =
      ∫ z,((register C l (OriginalRadialSeries.observed (profile R i per F B z)
          (raiseE (opened R N i per hi F (Z (i + 1))))))*
        (series C l (registered R N i per hi Q D u μ orders scale x F B z)).pass).part s
          ∂Gaussian.cloud ((model R N i per hi).covariance F tag) := by
  intro B
  rw [WilsonOriginalBoughtForestQ.original R N i per hi Q D u μ orders scale x F tag course lo B₀ l hl s]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only []
  rw [filed R N i per hi Q D u μ orders scale x F B z]

end YM.Integration.WilsonOriginalChargedForestQ
