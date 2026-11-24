import YM.Integration.WilsonOriginalSingleGaussianReceipt
import YM.Integration.WilsonOriginalFoldedUnaryIncome

/-! One genuinely funded new Wilson source in the complete finite normalized conditional. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedUnaryTable
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
  (u:V→MS.Rake.Label deck)(μ:ℝ)(orders:V→ℕ) (x:TestSpace (ActualRunQlocalNativeTuple.orbit D))
local notation "C" => Stock.census V
local notation "P₀" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "v₀" => (Bulk.Colors.noHole G (R.family.side (i + 1) per) C).vac
local notation "Y" => NativePaidPacketColors.colors P₀ v₀ x
local notation "S" => step R i per
local notation "K" => model R N i per hi

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)

local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))

open WilsonCoeffUV.Bank.Mosaic.Near IndependentSourcePathFamily OriginalMarkedSourceComet FundedOriginalMarkedInput


variable [Subsingleton V](v:V)
local notation "φ" => WilsonOriginalRelativeFoldedQuiet.relative R N i per hi F
  (WilsonVacuumPreResetOriginalOutput.covered R N i per)
local notation "word" => WilsonOriginalRegisteredRawPage.field R N i per hi Q D u μ orders x F
local notation "cᵢ" => WilsonOriginalChargedRawJet.weight D u N ((C).fire v)
local notation "production" => WilsonOriginalRegisteredFoldedDrivers.folded R N i per hi Q D u μ orders x F B

open WilsonOriginalSingleGaussianReceipt

private theorem centered_zero {A:Type}[CommRing A](F:PowerSeries A):
    constantCoeff (F-PowerSeries.C (constantCoeff F))=0:=by simp

private theorem phase_zero (prior:PChart G (fine R i per)):
    constantCoeff (WilsonOriginalRelativeFoldedQuiet.relative R N i per hi F prior)=0:=
  centered_zero _

def page (r:ℕ):Page (Precision.Key F G) (Woods G (coarse R i per)) (Source D u) C r where
  B:=flatten B
  source:=(C).fire v
  live:=singleton_nonempty _
  phase:=φ
  zero:=phase_zero R N i per hi F _
  mark:=word
  amplitude:=cᵢ
  driver:=production r
  written:=WilsonOriginalFoldedUnaryIncome.income R N i per hi Q D u μ orders x F B v r

local notation "W" => page R N i per hi Q D u μ orders x F B v
theorem original (r:ℕ) :
    realTable (W r) ((K).covariance F tag) ((K).symm F tag)=filed (W r) ((K).covariance F tag):=
  integral _ _ _

end YM.Integration.WilsonOriginalFoldedUnaryTable
