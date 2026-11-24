import YM.Integration.WilsonOriginalEarnedReefUnary
import YM.Integration.WilsonOriginalFoldedSourceVisit

/-! The original measured Q, its physical site and its native share of the folded Wick and winding expenditure. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRawQWindingVisit
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
open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))

open WilsonCoeffUV.Mer WilsonCoeffUV.Bank.Mosaic.Near IndependentSourcePathFamily OriginalMarkedSourceComet FundedOriginalMarkedInput


open WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open AnalyticNext.QuarticMatch.Sheets Next.Free
open WilsonOriginalFoldedSourceTicket
open WilsonOriginalFoldedUnarySourceEra (data reserve)
open WilsonMarkedIndependentRegisteredFoldedSeam (Bill)
open WilsonOriginalEarnedReefUnary (Tags readout)

def index (a:Source D u) : Count D u a.1.1.1 := (⟨a.1,rfl⟩,a.2.1)
def enrolled (a:Source D u) := WilsonOriginalChargedQSalary.lowered Q D u μ orders unit (fun _ : V=>a.2.2.1)
def grades (k:V→ℕ)(j:V) := max (k j) (WilsonOriginalChargedQSalary.grade D u j)
def sites (j:V):Cover:=lift (ActualRunQlocalNativeTuple.root D j)
def tests (a:Source D u):Case (OrbitD D):=SignedOriginalQCurvatureRows.tests D x (fun _ : V=>a.2.2.2)
local notation "idx" => index (R:=R) (i:=i) (per:=per) D u
local notation "full" => enrolled (R:=R) (i:=i) (per:=per) Q D u μ orders
local notation "gr" => grades (R:=R) (i:=i) (per:=per) D u
local notation "locations" => sites (R:=R) (i:=i) (per:=per) D
local notation "view" => tests (R:=R) (i:=i) (per:=per) D u x

private theorem eligible (k:V→ℕ)(a:Source D u):
    ((full a) a.1.1.1 (idx a)).rank ≤ gr k a.1.1.1+((full a) a.1.1.1 (idx a)).head:=by
  let j:=a.1.1.1
  let b:=idx a
  let z:=chosen Q D u μ orders unit (fun _ : V=>a.2.2.1) j b
  have hr:=WilsonOriginalChargedQSalary.degree Q D u μ orders unit (fun _ : V=>a.2.2.1) j b
  have hp:WilsonOriginalChargedQSalary.pole D u j b ≤ gr k j :=
    (Finset.le_sup (f:=WilsonOriginalChargedQSalary.pole D u j) (Finset.mem_univ b)).trans (le_max_right _ _)
  change WilsonOriginalChargedQSalary.pole D u j b ≤ z.rank at hr
  change z.rank ≤ gr k j+(z.rank-WilsonOriginalChargedQSalary.pole D u j b)
  omega

variable [Subsingleton V]

theorem represented (a:Source D u):
    let j:=a.1.1.1
    let X:=picked (full a) j (idx a)
    tuftV (touch (view a) {j}) (IndependentSourcePathFamily.independent X locations {j})=
      data (R:=R) (i:=i) (per:=per) Q D u μ orders x a:=by
  exact WilsonOriginalFoldedSourceTicket.material (full a) a.1.1.1 (idx a) locations (view a)

variable {e d c q t:ℕ}
include hi in
theorem original (a:Source D u)(k:V→ℕ)(j r:ℕ)
    (stage:Realm G (e+1) Credit.leanC)(anchor : stage.anchor ≤ i)
    {w σ:Gear G→ℝ}(hw:∀a,0<w a)
    (ready:FundedMarkedWindingWindow.ReceiptOn R {a.1.1.1} {a.1.1.1} a.1.1.1 (OrbitD D)
      (gr k) e j r d c q t w σ i stage anchor)
    (simple : G.Simple)(fund:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices fund R.kit)
    (colour:G.ColorIndex)(choice:Tags R)(fee:Cost):
    let s:=a.1.1.1
    let Y:=picked (full a) s (idx a)
    let P₀:=loose stage.draws i
    let cells:=(fun _ : V → Cover => cell P₀ locations)
    let ww:=4*max (w (stage.mint i anchor).gear) (stage.mint (i+1) (by omega)).σ
    let n₀:=coarse R i per
    let T:=data (R:=R) (i:=i) (per:=per) Q D u μ orders x a
    let H:=WilsonMarkedIndependentFoldedIntegral.folded R N i (gr k s) T.1 n₀
    let Y₀:=IndependentSourcePathFamily.independent Y locations
    let outputRow := coilH R.family.path.levels R.metals.O i N n₀ Y₀ (gr k) fee {s}
    Bill R stage anchor N per s j r d c q t (gr k) Y cells w σ ∧
      OriginalIssuedMarkedRows.fee (k:=gr k) Y stage anchor w=
        charge (full a) (gr k) e ww s (idx a) ∧
      pPly (view a) {s} outputRow=Blue.mix fee H ∧
      flash H=readout R N i per Q D u μ orders x colour choice a :=by
  intro s Y P₀ cells ww n₀ T H Y₀ outputRow
  have visit:=WilsonOriginalFoldedSourceVisit.ticket R colour choice per s (full a) (idx a)
    (eligible (R:=R) (i:=i) (per:=per) Q D u μ orders k a) locations j r stage anchor hw ready simple fund paid hi fee
  obtain ⟨_,priced,winding,allTest⟩:=visit
  have read:=allTest (view a)
  unfold WilsonMarkedIndependentRegisteredFoldedIntegral.Read at read
  dsimp only at read
  have core:=represented (R:=R) (i:=i) (per:=per) Q D u μ orders x a
  dsimp only at core
  rw [core] at read
  have mk:mass (gr k) {s}=gr k s:=by simp [mass]
  rw [mk] at read
  exact ⟨winding,priced,read.1,read.2⟩

end YM.Integration.WilsonOriginalRawQWindingVisit
