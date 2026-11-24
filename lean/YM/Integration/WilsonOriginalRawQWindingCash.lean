import YM.Integration.WilsonOriginalRawQWindingLedger

/-! One rooted spatial and coupling estimate for the complete signed enrolled Q source at the nonbare date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRawQWindingCash
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


open WilsonOriginalRawQWindingVisit (index enrolled grades)


open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider.Canvas ActualRunAdmissionScales
open WilsonOriginalRawQWindingLedger (invoice share)
open WilsonOriginalRawQWindingVisit (sites tests)
open WilsonMarkedIndependentRegisteredFoldedSeam

private theorem pool {A:Type*}[Fintype A] (z B cost:A→ℝ) (slow fast price:ℝ)
    (pos:∀a,0≤z a)(ok:0≤fast)(all:∀a,B a*slow≤fast*cost a)
    (budget:∑a,z a*cost a≤price):
    (∑a,z a*B a)*slow≤fast*price:=by
  rw [Finset.sum_mul]
  calc
    _ ≤ ∑a,fast*(z a*cost a):=by
      apply Finset.sum_le_sum
      intro a _
      calc z a*B a*slow = z a*(B a*slow):=mul_assoc .. 
           _ ≤ z a*(fast*cost a):=mul_le_mul_of_nonneg_left (all a) (pos a)
           _ = _:=by ring
    _ = fast*∑a,z a*cost a:=(Finset.mul_sum ..).symm
    _ ≤ fast*price:=mul_le_mul_of_nonneg_left budget ok

variable [Subsingleton V] (v:V) {e d c q t:ℕ}
local notation "gr" => grades R i per D u
local notation "full" => enrolled R i per Q D u μ orders
local notation "idx" => index R i per D u
local notation "points" => sites R i per D
local notation "view" => tests R i per D u x
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family N per (i+1)
local notation "amps" => weight D u N ((Stock.census V).fire v)

def windingRow (k:V→ℕ)(j r:ℕ)(stage:Realm G (e+1) Credit.leanC)(a:Source D u) :
    (V → Cover) → Ten (Pen (OrbitD D) {a.1.1.1}) (Cloth (Hooks G)) r:=
  let s:=a.1.1.1
  let selected:=picked (full a) s (idx a)
  let cells:=(fun _ : V → Cover => cell (loose stage.draws i) points)
  WilsonMarkedIndependentRegisteredFoldedSeam.row R stage N i per s j r (gr k) selected cells

include hi x in
theorem original (k:V→ℕ)(j r:ℕ)(stage:Realm G (e+1) Credit.leanC)(anchor:stage.anchor ≤ i)
    {w σ:Gear G→ℝ}(hw:∀a,0<w a)
    (ready:FundedMarkedWindingWindow.ReceiptOn R {v} {v} v (OrbitD D) (gr k) e j r d c q t w σ i stage anchor)
    (simple:G.Simple)(fund:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices fund R.kit)
    (colour:G.ColorIndex)(choice:Tags R)(band:|g₁|≤1):
    let gear:=(stage.mint i anchor).gear
    let width:=4*max (w gear) (stage.mint (i+1) (by omega)).σ
    let rent:=2*∑b:Bool,invoice R i per Q D u μ orders k e width b
    let tail:=Real.exp (-(σ gear/512)*((R.family.side i per).val:ℝ))
    ∃B:Source D u→ℝ,
      (∀a:Source D u,PostMark (D:=OrbitD D) (α:=Hooks G) {a.1.1.1} a.1.1.1 r (windingRow R N i per Q D u μ orders k j r stage a) (σ gear/32/2/2/2) (B a) d) ∧
      (∑a,‖amps a‖*B a)*g₁^(-(c:ℝ))≤g₁^q*rent ∧
      (∑a,‖amps a‖*B a)≤(admittedCost R.family.path.levels i)^t*(tail*rent):=by
  intro gear width rent tail
  let cost:=share R i per Q D u μ orders k e width
  let z:Source D u→ℝ:=fun a=>‖amps a‖
  have hg:0<g₁:=ActualRunKernelPackets.regulator_pos R N per (i+1) hi
  have willing (a:Source D u):∃B:ℝ,B*g₁^(-(c:ℝ))≤g₁^q*cost a ∧
      B≤(admittedCost R.family.path.levels i)^t*(tail*cost a) ∧
      PostMark {a.1.1.1} a.1.1.1 r (windingRow R N i per Q D u μ orders k j r stage a) (σ gear/32/2/2/2) B d:=by
    let s:=a.1.1.1
    have origin:s=v:=Subsingleton.elim _ _
    have bought:FundedMarkedWindingWindow.ReceiptOn R {s} {s} s (OrbitD D) (gr k) e j r d c q t w σ i stage anchor:=by simpa only [origin] using ready
    have got:=WilsonOriginalRawQWindingVisit.original R N i per hi Q D u μ orders x a k j r stage anchor hw bought simple fund paid colour choice (ratioHigh R.family.path.levels R.metals.O N i)
    obtain ⟨b,fin,seam,rooted⟩:=got.1
    have fee:=got.2.1
    rw [fee] at fin seam
    exact ⟨b,fin,seam,rooted⟩
  choose B fit winding rooted using willing
  have totals:∑a,z a*cost a≤rent:=WilsonOriginalRawQWindingLedger.weighted R N i per Q D u μ orders k e width v band
  have hC:0≤admittedCost R.family.path.levels i:=(zero_le_one.trans (admittedCost_one ..))
  refine ⟨B,rooted,pool z B cost _ _ _ (fun _=>norm_nonneg _) (pow_nonneg hg.le q) fit totals,?_⟩
  rw [←mul_assoc]
  simpa only [mul_one] using pool z B cost 1 ((admittedCost R.family.path.levels i)^t*tail) rent
    (fun _=>norm_nonneg _) (mul_nonneg (pow_nonneg hC _) (Real.exp_nonneg _))
    (fun a=>by simpa only [mul_one,mul_assoc] using winding a) totals

end YM.Integration.WilsonOriginalRawQWindingCash
