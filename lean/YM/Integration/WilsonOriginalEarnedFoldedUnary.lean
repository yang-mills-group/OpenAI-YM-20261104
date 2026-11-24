import YM.Integration.WilsonOriginalEarnedUnaryRaw
import YM.Integration.WilsonOriginalFoldedUnarySourceEra

/-! The occupied finite Wilson log on the authenticated earned course and its independent original marked Wick column. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalEarnedFoldedUnary
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

def independent (k:V→ℕ)(a:Source D u) :=
  WilsonOriginalFoldedMarkedRightColumn.filed R N i per F
    (reserve (R:=R) (i:=i) (per:=per) D u k a)
    ((data (R:=R) (i:=i) (per:=per) Q D u μ orders x a).1 (fine R i per))

theorem numerator_eq (simple:G.Simple)(B₀:Stationary.Link G (coarse R i per))(l:ℕ)
    (k:V→ℕ)(a:Source D u):
    let W:=payer R N i per hi Q D u μ orders x F v B₀ l
    numerator W q₀ a=mass W q₀ * flash (independent R N i per Q D u μ orders x F k a):=by
  intro W
  let T:=data (R:=R) (i:=i) (per:=per) Q D u μ orders x a
  let j:=reserve (R:=R) (i:=i) (per:=per) D u k a
  have paid:=WilsonOriginalFoldedUnarySourceEra.admitted (R:=R) (i:=i) (per:=per) Q D u μ orders x k a
  have rep:=WilsonOriginalFoldedUnarySourceEra.represented R N i per hi Q D u μ orders x F a
  have h:=WilsonOriginalFoldedMarkedRightColumn.normalized R N i per hi F tag simple j (T.1 (fine R i per))
    (paid.span _) (paid.pale _)
  change Wick _ q₀ (raiseE W.phase*(WilsonOriginalRegisteredRawPage.field R N i per hi Q D u μ orders x F a))=_
  rw [←rep]
  exact h

theorem priced_row (simple:G.Simple)(B₀:Stationary.Link G (coarse R i per))(l:ℕ)(k:V→ℕ) :
    let W:=payer R N i per hi Q D u μ orders x F v B₀ l
    row W q₀=∑a,W.amplitude a • register C l (observed W.B (flash (independent R N i per Q D u μ orders x F k a))):=by
  intro W
  apply WilsonOriginalSingleGaussianDivision.identified W q₀ ((K).symm F tag)
  intro a
  rw [numerator_eq R N i per hi Q D u μ orders x F tag v simple B₀ l k a, map_mul]

theorem original (simple:G.Simple){m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}
    (bank:Issued R N (i+1) e (Z (i+1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(l:ℕ)(hl:l ≤ e+2)(k:V→ℕ) :
    let W:=payer R N i per hi Q D u μ orders x F v B₀ l
    let I₀:=NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x
    let actual:=Bulk.Fk K F tag I₀ (B₁ B₀) l
    let outside:=WilsonOriginalSingleMarkedRegister.token C l W.source*
      (∑a,W.amplitude a • register C l (observed W.B (flash (independent R N i per Q D u μ orders x F k a))))
    ratio actual=1+outside ∧ logMarked actual=outside :=by
  intro W I₀ actual outside
  have h:=WilsonOriginalEarnedUnaryRaw.original R N i per hi Q D u μ orders x F tag v course lo bank B₀ l hl
  have e:WilsonOriginalSingleMarkedRegister.token C l W.source*row W q₀=outside :=
    congrArg (fun T=>WilsonOriginalSingleMarkedRegister.token C l W.source*T)
      (priced_row R N i per hi Q D u μ orders x F tag v simple B₀ l k)
  exact ⟨h.1.trans (congrArg (1+·) e),h.2.trans e⟩

end YM.Integration.WilsonOriginalEarnedFoldedUnary
