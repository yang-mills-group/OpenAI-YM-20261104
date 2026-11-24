import YM.Integration.WilsonOriginalEarnedFoldedUnary
import YM.Integration.WilsonOriginalFoldedFiledForest

/-! The actual registered source at the original issued date, in the independently computed normalized Reef integral. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalEarnedReefUnary
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


variable [Subsingleton V](v:V)
open WilsonOriginalSingleGaussianReceipt
local notation "B₁" => (fun B₀=>Stationary.arm G (coarse R i per) 1 B₀)

open WilsonOriginalFoldedUnarySourceEra (data reserve)
open WilsonOriginalFoldedMarkedRightColumn (before)
open WilsonOriginalSingleGaussianDivision (row)
open WilsonOriginalEarnedUnaryRaw (payer)
open OriginalRadialSeries (observed)
local notation "q₀" => ((model R N i per hi).covariance F tag)


open FormalBulk08 Flat Reef Orb Jets Shore Lava Wine Gorge Lotus Mesa
open AnalyticNext.QuarticMatch.Sheets Next.Free
local notation "lvl" => R.family.path.levels
local notation "wood" => (fun j:ℕ=>Flat.routes (R.family.path.levels.clock.op j 0).patch)
local notation "br" => (fun j:ℕ=>(R.family.path.levels.blocks j 0).branches)
local notation "F₀" => repeatF (step R i per)
local notation "n₀" => coarse R i per
abbrev Tags (R₁:Run G) := ∀j n,(primary (R₁.family.path.levels.clock.op j 0).patch R₁.family.path.levels.clock.kernel n).Choices
variable (colour:G.ColorIndex)

def readout (calendar:Tags R) (a:Source D u) : Ink (Woods G (coarse R i per)) :=
  let T:=data (R:=R) (i:=i) (per:=per) Q D u μ orders x a
  let path:=destination lvl N i
  let prior:=Dove.model lvl wood br R.metals.O colour N (i+1)
  Reef.tossed path R.metals.O (br i) (wood i) n₀ (calendar i n₀)
    (Mesa.stone prior (n₀*path.L)) (flash (T.1 (n₀*path.L)))

omit [Subsingleton V] in
include hi in
theorem signed (choice:Tags R)(simple:G.Simple)(fund:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices fund R.kit)
    (k:V→ℕ)(a:Source D u) :
    flash (WilsonOriginalEarnedFoldedUnary.independent R N i per Q D u μ orders x F₀ k a)=
      readout R N i per Q D u μ orders x colour choice a :=
  WilsonOriginalFoldedFiledForest.normalized R N i per colour choice simple fund rows hi _ _
    (WilsonOriginalFoldedUnarySourceEra.admitted (R:=R) (i:=i) (per:=per) Q D u μ orders x k a)

theorem original (choice:Tags R)(simple:G.Simple)(fund:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices fund R.kit)
    {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}
    (bank:Issued R N (i+1) e (Z (i+1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(l:ℕ)(hl:l ≤ e+2) :
    let W:=payer R N i per hi Q D u μ orders x F₀ v B₀ l
    let I₀:=NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x
    let actual:=Bulk.Fk K F₀ tag I₀ (B₁ B₀) l
    let outside:=WilsonOriginalSingleMarkedRegister.token C l W.source*
      (∑a,W.amplitude a • register C l (OriginalRadialSeries.observed W.B (readout R N i per Q D u μ orders x colour choice a)))
    ratio actual=1+outside ∧ logMarked actual=outside:=by
  intro W I₀ actual outside
  let k:V→ℕ:=fun _=>0
  have e (a:Source D u):flash (WilsonOriginalEarnedFoldedUnary.independent R N i per Q D u μ orders x F₀ k a)=
      readout R N i per Q D u μ orders x colour choice a:=
    signed R N i per hi Q D u μ orders x colour choice simple fund rows k a
  have same:=WilsonOriginalEarnedFoldedUnary.original R N i per hi Q D u μ orders x F₀ tag v simple course lo bank B₀ l hl k
  dsimp only at same
  simp only [e] at same
  exact same

end YM.Integration.WilsonOriginalEarnedReefUnary
