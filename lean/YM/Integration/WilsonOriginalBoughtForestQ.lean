import YM.Integration.SignedOpeningMarkedVertices
import YM.Integration.WilsonOriginalMeasuredOccupiedForest

/-! The original registered Q at any admitted date, in the actual charged finite Gaussian with its inherited quiet law. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalBoughtForestQ
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

private theorem legal : Bulk.Well Y :=by
  have H:=ActualOriginalQFrozenInput.packets_paid Q D u μ orders N 1 ((levels R).budget (i + 1))
    (fun _=>1) 1 zero_lt_one (fun _=>zero_lt_one)
  have law:=(Bulk.Colors.no_hole G (R.family.side (i + 1) per) C).1
  exact NativePaidPacketColors.colors_well H one_ne_zero v₀ law.suppose_vac law.natural law.envelope _

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)
variable (z:Precision.Key F G→ℝ)
local notation "M" => saddle R N i per F

def published : PTable C := PowerSeries.mk fun d => lit C fun J=>
  ∑ a:SignedOpeningMarkedVertices.Source D u, SignedOpeningMarkedVertices.multiplier D u J.val a *
    (MvPolynomial.eval (SignedRegisteredKernelPolynomial.focus F B z)
      (coeff d (SignedOpeningMarkedVertices.supplied Q D u μ orders scale K F M x a)):ℝ)

include tag in
theorem matched :
    names R N i per hi F Y B z=published R N i per hi Q D u μ orders scale x F B z:=by
  have h:=(model R N i per hi).hessian_pos F tag
  rw [OriginalMarkedHeatCovariance.precision R N i per hi F tag] at h
  have projected:M=reveal G S F*((reveal G S F).transpose*M):=by
    apply sweeps G S F (prediction R N i per) (lower R N i) (isUnit_iff_ne_zero.mpr h.det_pos.ne')
    exact horizon_step (levels R) i N hi _ _ (step R i per).sizes
  apply PowerSeries.ext
  intro j
  rw [names,published,coeff_mk,coeff_mk]
  apply congrArg (lit C)
  funext J
  have actual:=PhysicalForestMarkedRay.coefficient S F M K B z tag Y (legal R N i per Q D u μ orders scale x) J projected ((NativePaidPacketColors.colors P v₀ (fun j=>scale j • x j)).power J + j)
  have source:=SignedOpeningMarkedVertices.kernel Q D u μ orders scale K F M N hi
    ((levels R).budget (i + 1)) v₀ projected J x B z j
  dsimp only [] at source
  rw [Assembly.reading] at source
  exact actual.symm.trans source

theorem original {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i)
    (B₀:Stationary.Link G (coarse R i per))(l:ℕ)(hl:l ≤ e + 2)(s:(Board C l).Mode):
    let B:=Stationary.arm G _ 1 B₀
    (Bulk.Fk K F tag (QuadraticLocal.Fk.grant (π (i + 1)) (Step.tape (e+2)) Y) B l).part s =
      ∫ z,((register C l (OriginalRadialSeries.observed (profile R i per F B z)
          (raiseE (opened R N i per hi F (Z (i + 1))))))*
        (series C l (published R N i per hi Q D u μ orders scale x F B z)).pass).part s
          ∂Gaussian.cloud ((model R N i per hi).covariance F tag) :=by
  intro B
  rw [course.filed i lo hi per F tag Y (legal R N i per Q D u μ orders scale x) B₀ l hl s]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  dsimp only []
  unfold numerator
  rw [matched R N i per hi Q D u μ orders scale x F tag B z]

end YM.Integration.WilsonOriginalBoughtForestQ
