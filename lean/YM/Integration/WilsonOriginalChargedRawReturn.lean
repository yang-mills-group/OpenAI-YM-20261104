import YM.Integration.WilsonOriginalChargedRawWick
import YM.Integration.FVA1Physical.Wilson.RecastColors
import YM.Integration.WilsonOriginalMixedFiniteMaterial

/-! The full independently computed conditional Wick table, logarithm and actual scalar reset re-enter the original old-plus-fresh program on every group field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalChargedRawReturn
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

open FVA1Physical.Wilson QuadraticLocal.Sunrise QuadraticLocal.Earn
open WilsonVacuumPreResetDatedDeposit (Issued)
variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
variable (r:ℕ)(grades:V→ℕ)(cost:Adjacent.UnitCost)(coarseBank:Bulk.Colors (Stock.census V) G (coarse R i per))

/-- The ordinary, unprojected Wick table is computed from the original registered raw path vertices. -/
def table (Z:SeriesA G)(B₀:Stationary.Link G (coarse R i per)) : Order.Grade (C) r :=
  let B := Stationary.arm G _ 1 B₀
  Cloud.prescription ((model R N i per hi).covariance F tag) ((model R N i per hi).symm F tag) 0
    (WilsonOriginalChargedRawWick.atoms R N i per hi Q D u μ orders x F B Z r)

private def counterterm (Z:SeriesA G)(s:Hot (C))(j:ℕ)(b:fieldDir G (coarse R i per) 1) : ℂ :=
  Adjacent.born (fun k y => (Order.observe (C) r (Order.logMarked
    (table R N i per hi Q D u μ orders x F tag r Z y)) k).part s.val)
    cost 0 r j ((Stationary.arm G _ 1).symm b)

/-- The incoming old marks on the very next group field, with the original measured coupling reset. -/
def prior (Z:SeriesA G) : Bulk.Colors (C) G (coarse R i per) where
  vac := coarseBank.vac
  power s := Launch.index (C) grades s.val+1
  mark s t U := clockPacket (Launch.index (C) grades s.val+1) r
    (counterterm R N i per hi Q D u μ orders x F tag r cost Z s) (t,forestLog U)

variable {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
  (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}
  (bank:Issued R N (i + 1) e (Z (i + 1)) σ cash)(hr:r ≤ e + 2)
local notation "raw" => NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x

include course lo bank hr
theorem recorded (B₀:Stationary.Link G (coarse R i per)) :
    Bulk.Fk K F tag (raw) (Stationary.arm G _ 1 B₀) r =
      table R N i per hi Q D u μ orders x F tag r (Z (i+1)) B₀ := by
  ext1 s
  exact WilsonOriginalChargedRawWick.deposited R N i per hi Q D u μ orders x F tag course lo bank B₀ r hr s

theorem original :
    recastColors K F tag (raw) grades r cost coarseBank =
      prior R N i per hi Q D u μ orders x F tag r grades cost coarseBank (Z (i+1)) := by
  have fixed (s:Hot (C)) : loopReset K F tag (raw) s r cost =
      counterterm R N i per hi Q D u μ orders x F tag r cost (Z (i+1)) s := by
    funext j b
    unfold loopReset counterterm
    simp only [recorded R N i per hi Q D u μ orders x F tag r course lo bank hr]
  have marks (s:Hot (C)) : germPainter K F tag (raw) grades s r cost =
      fun t U => clockPacket (Launch.index (C) grades s.val + 1) r
        (counterterm R N i per hi Q D u μ orders x F tag r cost (Z (i+1)) s) (t,forestLog U) := by
    funext t U
    unfold germPainter
    rw [fixed]
  unfold recastColors prior
  simp only [marks]

/-- Fresh inputs are joined only after the complete nonbare logarithm and its signed old source have returned. -/
theorem joined (old fresh:Finset V)(born:Bulk.Colors (C) G (coarse R i per)) :
    WilsonOriginalMixedFiniteMaterial.bank old fresh (recastColors K F tag (raw) grades r cost coarseBank) born =
    WilsonOriginalMixedFiniteMaterial.bank old fresh
      (prior R N i per hi Q D u μ orders x F tag r grades cost coarseBank (Z (i+1))) born := by
  rw [original R N i per hi Q D u μ orders x F tag r grades cost coarseBank course lo bank hr]

end YM.Integration.WilsonOriginalChargedRawReturn
