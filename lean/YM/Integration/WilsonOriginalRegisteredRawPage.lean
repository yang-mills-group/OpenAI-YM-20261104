import YM.Integration.WilsonOriginalRegisteredFoldedQ
import YM.Integration.WilsonOriginalLoweredChartSource
import YM.Integration.WilsonOriginalChargedQSalary

/-! The funded, independently declared lowered-head Wilson source, its true Laurent weights and actual physical finite Wick driver. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRegisteredRawPage
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
variable (z:Precision.Key F G→ℝ)
local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))

open WilsonCoeffUV.Bank.Mosaic.Near IndependentSourcePathFamily OriginalMarkedSourceComet FundedOriginalMarkedInput

private abbrev row (a:Source D u) : Count D u a.1.1.1 := (⟨a.1,rfl⟩,a.2.1)
private abbrev old (a:Source D u) := chosen Q D u μ orders unit (fun _ : V=>a.2.2.1) a.1.1.1 (row (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) a)
private abbrev seed (a:Source D u) := WilsonOriginalChargedQSalary.lowered Q D u μ orders unit
  (fun _ : V=>a.2.2.1) a.1.1.1 (row (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) a)
private abbrev test (a:Source D u) := SignedOriginalQCurvatureRows.tests D x (fun _ : V=>a.2.2.2)
private abbrev site (a:Source D u) := lift (origin D u a)

def field (a:Source D u) : Ink (Active G F⊕Woods G (coarse R i per)) :=
  SignedOpeningSourceCurrent.independent K F M a.1.1.1 (seed (R:=R) (i:=i) (per:=per) (Q:=Q) (D:=D) (u:=u) (μ:=μ) (orders:=orders) a) (test (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) (x:=x) a) (site (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) a)

omit [Fintype V] in
theorem coefficient (a:Source D u)(d:ℕ) :
    coeff (d+debt D (u:=u) a.1) (supplied Q D u μ orders unit K F M x a) =
    coeff d (field R N i per hi Q D u μ orders x F a) :=by
  exact WilsonOriginalLoweredChartSource.coefficient R N i per hi F a.1.1.1
    (old (R:=R) (i:=i) (per:=per) (Q:=Q) (D:=D) (u:=u) (μ:=μ) (orders:=orders) a) (test (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) (x:=x) a) (site (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) a) (debt D (u:=u) a.1) rfl
    (WilsonOriginalChargedQSalary.degree Q D u μ orders unit (fun _ : V=>a.2.2.1) _ (row (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) a)) d

theorem funded (k:V→ℕ)(cap:ℕ){w:ℝ}(hw:0<w)(Z:Finset V)(sites:V → Cover)(b:Bool) :
    let ranks:=fun a=>max (k a) (WilsonOriginalChargedQSalary.grade D u a)
    let trueRows:=WilsonOriginalChargedQSalary.lowered Q D u μ orders unit (fun _ : V=>b)
    let price:=bill (chosen Q D u μ orders unit (fun _ : V=>b)) ranks cap w
    let K':=independent trueRows sites
    0≤price ∧ Eu ranks K' ∧ K' ∅=0 ∧ safeB sites K' Z cap (steep w) price :=
  WilsonOriginalChargedQSalary.funded Q D u μ orders unit (fun _ : V=>b) k cap hw Z sites

/-- The whole actual finite occupied kernel, including the charge of every angular rank and repeated original seat. -/
theorem driver (d:ℕ)(J:(C).Mode) :
    WilsonOriginalChargedRawWick.charged R N i per hi Q D u μ orders x F B d J =
      ∑ a:Source D u, weight D u N J a • SignedRegisteredMarkedProgram.register F B
        (coeff d (field R N i per hi Q D u μ orders x F a)) :=by
  apply Finset.sum_congr rfl
  intro a _
  rw [coefficient R N i per hi Q D u μ orders x F a d]

end YM.Integration.WilsonOriginalRegisteredRawPage
