import YM.Integration.WilsonOriginalRegisteredRawPage
import YM.Integration.WilsonOriginalFoldedMarkedRightColumn

/-! The independently graded original one-source input on every finite side and its held physical column. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedUnarySourceEra
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

open WilsonCoeffUV.Mer WilsonCoeffUV.Bank.Mosaic.Near IndependentSourcePathFamily OriginalMarkedSourceComet FundedOriginalMarkedInput

private abbrev row (a:Source D u) : Count D u a.1.1.1 := (⟨a.1,rfl⟩,a.2.1)

private abbrev seed (a:Source D u) := WilsonOriginalChargedQSalary.lowered Q D u μ orders unit
  (fun _ : V=>a.2.2.1) a.1.1.1 (row (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) a)
private abbrev test (a:Source D u) := SignedOriginalQCurvatureRows.tests D x (fun _ : V=>a.2.2.2)
private abbrev site (a:Source D u) := lift (origin D u a)

local notation "z₀" => seed (R:=R) (i:=i) (per:=per) (Q:=Q) (D:=D) (u:=u) (μ:=μ) (orders:=orders)
local notation "x₀" => test (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) (x:=x)
local notation "y₀" => site (R:=R) (i:=i) (per:=per) (D:=D) (u:=u)
def data (a:Source D u) : Era G ℝ :=
  let z:=z₀ a
  let j:=a.1.1.1
  tuftV (touch (x₀ a) {j}) (OriginalMarkedSourceComet.source (OrbitD D) j
    (colour z.path z.color z.weight z.quadrant) z.knob z.point z.head (y₀ a))

def reserve (k:V→ℕ)(a:Source D u) := max (k a.1.1.1) (WilsonOriginalChargedQSalary.grade D u a.1.1.1)

theorem admitted (k:V→ℕ)(a:Source D u) :
    Auth (reserve (R:=R) (i:=i) (per:=per) D u k a) (data (R:=R) (i:=i) (per:=per) Q D u μ orders x a):=by
  let z:=z₀ a
  let b:=row (R:=R) (i:=i) (per:=per) (D:=D) (u:=u) a
  have hr:=WilsonOriginalChargedQSalary.degree Q D u μ orders unit (fun _ : V=>a.2.2.1) a.1.1.1 b
  have hp:WilsonOriginalChargedQSalary.pole D u a.1.1.1 b ≤ reserve (R:=R) (i:=i) (per:=per) D u k a :=
    (Finset.le_sup (f:=WilsonOriginalChargedQSalary.pole D u a.1.1.1) (Finset.mem_univ b)).trans (le_max_right _ _)
  have fits:z.rank ≤ reserve (R:=R) (i:=i) (per:=per) D u k a+z.head :=by
    let n₀:=(chosen Q D u μ orders unit (fun _ : V=>a.2.2.1) a.1.1.1 b).rank
    change WilsonOriginalChargedQSalary.pole D u a.1.1.1 b ≤ n₀ at hr
    change n₀ ≤ reserve (R:=R) (i:=i) (per:=per) D u k a+(n₀-WilsonOriginalChargedQSalary.pole D u a.1.1.1 b)
    omega
  exact (OriginalMarkedSourceComet.certified (OrbitD D) a.1.1.1 _
    (OriginalMarkedSourceComet.invariant z.path z.color z.weight z.quadrant)
    z.knob z.point z.head _ fits (y₀ a)).tuft (touch (x₀ a) {a.1.1.1})

omit [Fintype V] in
theorem represented (a:Source D u) :
    WilsonOriginalFoldedMarkedRightColumn.before R N i per hi F ((data (R:=R) (i:=i) (per:=per) Q D u μ orders x a).1 (fine R i per))=
      WilsonOriginalRegisteredRawPage.field R N i per hi Q D u μ orders x F a:=rfl

end YM.Integration.WilsonOriginalFoldedUnarySourceEra
