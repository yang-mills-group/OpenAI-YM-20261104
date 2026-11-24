import YM.Integration.WilsonOriginalRegisteredFoldedDrivers
import YM.Integration.WilsonOriginalScalarGaussianFold

/-! The original normalized registered Q read on one elected nonbare chart uses the periodic folded action. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRegisteredFoldedQ
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
local notation "P" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "v₀" => (Bulk.Colors.noHole G (R.family.side (i + 1) per) C).vac
local notation "Y" => NativePaidPacketColors.colors P v₀ x
local notation "S" => step R i per
local notation "K" => model R N i per hi

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)
local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))


open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRegisteredFoldedDrivers (folded)
open WilsonOriginalRelativeFoldedQuiet (credit)

theorem original {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}
    (bank:Issued R N (i+1) e (Z (i+1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(l:ℕ)(hl:l ≤ e+2) :
    let B:=Stationary.arm G _ 1 B₀
    let raw:=NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x
    let Y₁:=Bulk.Fk K F tag raw B l
    let Y₂:=Cloud.prescription ((K).covariance F tag) ((K).symm F tag) 0
      (folded R N i per hi Q D u μ orders x F B l)
    ratio Y₁=ratio Y₂ ∧ logMarked Y₁=logMarked Y₂ :=by
  intro B raw Y₁ Y₂
  let genuine:=WilsonOriginalChargedRawWick.atoms R N i per hi Q D u μ orders x F B (Z (i+1)) l
  have filedTable:Y₁=Cloud.prescription ((K).covariance F tag) ((K).symm F tag) 0 genuine:=by
    ext1 s
    exact WilsonOriginalChargedRawWick.deposited R N i per hi Q D u μ orders x F tag course lo bank B₀ l hl s
  let scalar:=credit (WilsonVacuumPreResetDepositedRay.filed R N i per (Z (i+1))) (covered R N i per)
  have result:ratio Y₁=ratio Y₂:=by
    rw [filedTable]
    exact WilsonOriginalScalarGaussianFold.normalized _ _ _ genuine _
      (WilsonVacuumPreResetFiniteRegister.register C l scalar)
      (WilsonOriginalRegisteredFoldedDrivers.zero scalar l (WilsonOriginalRegisteredFoldedDrivers.credit_zero ..))
      (WilsonOriginalRegisteredFoldedDrivers.vacant scalar l)
      (WilsonOriginalRegisteredFoldedDrivers.actual R N i per hi Q D u μ orders x F B (Z (i+1)) e l bank hl)
  exact ⟨result,congrArg Extra.Trajectories.connected result⟩

end YM.Integration.WilsonOriginalRegisteredFoldedQ
