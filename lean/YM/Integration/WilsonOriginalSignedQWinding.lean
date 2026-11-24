import YM.Integration.WilsonOriginalRawQWindingCash
import YM.Integration.WilsonRegisteredTwoBirthWindingSum

/-! A bounded signed hearing of the entire single-source winding difference, including every native real/imaginary component. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedQWinding
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

variable [Subsingleton V] (v:V) {e d c q t:ℕ}
local notation "gr" => grades R i per D u
local notation "full" => enrolled R i per Q D u μ orders
local notation "idx" => index R i per D u
local notation "points" => sites R i per D
local notation "view" => tests R i per D u x
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family N per (i+1)
local notation "amps" => weight D u N ((Stock.census V).fire v)


open WilsonOriginalRawQWindingCash (windingRow)
open WilsonRegisteredTwoBirthWindingSum (heard)

include hi x in
theorem original (k:V→ℕ)(j r:ℕ)(stage:Realm G (e+1) Credit.leanC)(anchor:stage.anchor ≤ i)
    {w σ:Gear G→ℝ}(hw:∀a,0<w a)(hs:0≤σ (stage.mint i anchor).gear)
    (ready:FundedMarkedWindingWindow.ReceiptOn R {v} {v} v (OrbitD D) (gr k) e j r d c q t w σ i stage anchor)
    (simple:G.Simple)(fund:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices fund R.kit)
    (colour:G.ColorIndex)(choice:Tags R)(band:|g₁|≤1):
    let gear:=(stage.mint i anchor).gear
    let width:=4*max (w gear) (stage.mint (i+1) (by omega)).σ
    let rent:=2*∑b:Bool,invoice R i per Q D u μ orders k e width b
    let tail:=Real.exp (-(σ gear/512)*((R.family.side i per).val:ℝ))
    ∀z:Source D u→ℂ,
      (∀a:Source D u,heard {a.1.1.1} a.1.1.1 r (windingRow R N i per Q D u μ orders k j r stage a) (z a)) →
      ‖∑a,amps a*z a‖*g₁^(-(c:ℝ)) ≤ g₁^q*rent ∧
        ‖∑a,amps a*z a‖ ≤ (admittedCost R.family.path.levels i)^t*(tail*rent):=by
  intro gear width rent tail z readings
  obtain ⟨B,rooted,price,spatial⟩:=WilsonOriginalRawQWindingCash.original R N i per hi Q D u μ orders x v k j r stage anchor hw ready simple fund paid colour choice band
  have lower (a:Source D u):‖z a‖≤B a:=by
    obtain ⟨pointed,angles,signs,unitTest,unitSign,h⟩:=readings a
    rw [h]
    have test:=SignedRootedWindingReadout.tested {a.1.1.1} (Finset.mem_singleton_self _) (by positivity) (rooted a) pointed angles 1 (by norm_num) unitTest signs unitSign
    simpa only [one_mul] using test.2
  have bound:‖∑a,amps a*z a‖≤∑a,‖amps a‖*B a:=by
    calc _ ≤ ∑a,‖amps a*z a‖:=norm_sum_le .. 
         _ ≤ _:=by apply Finset.sum_le_sum;intro a _;rw [norm_mul];exact mul_le_mul_of_nonneg_left (lower a) (norm_nonneg _)
  have hg:=ActualRunKernelPackets.regulator_pos R N per (i+1) hi
  exact ⟨(mul_le_mul_of_nonneg_right bound (Real.rpow_nonneg hg.le _)).trans price,bound.trans spatial⟩
end YM.Integration.WilsonOriginalSignedQWinding
