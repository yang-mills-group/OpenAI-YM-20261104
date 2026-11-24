import YM.Integration.WilsonOriginalRawQWindingLedger
import YM.Integration.WilsonOriginalProjectedCurvatureLoan

/-! Elect one original realm before either regulator or any of the point-source positions. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalQWindingAppointment
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


theorem rank (j:V):WilsonOriginalChargedQSalary.grade D u j ≤ ActualOriginalQLayout.rankCap R u:=by
  apply Finset.sup_le
  intro b _
  exact (ActualRunKernelPackets.term_grade R (ActualOriginalQPackets.degree u) b.1.val).trans
    (WilsonOriginalProjectedCurvatureBudget.limit u b.1.val)

theorem scheduled (k:V→ℕ)(fixed:∀j,ActualOriginalQLayout.rankCap R u≤k j):
    grades R i per D u k=k:=by
  funext j
  exact max_eq_left ((rank R i per D u j).trans (fixed j))

theorem original (dims k:Fin 1→ℕ)(e j r d:ℕ)(grade:j≤e)(w:Gear G→ℝ)(hw:∀I,0<w I):
    ∃(fund:ℕ→Gear G→ℝ)(σ:Gear G→ℝ)(t:ℕ), (∀I,0<σ I) ∧
      (∀i I,(σ I)⁻¹≤fund i I) ∧ WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G fund) ∧
      ∀(R:Run G)(_ : G.Simple),RG05Preconstruction.ReadoutPurchase R.b → FundedMarkedCoverRows.prices fund R.kit → ∀c q:ℕ,
      ∀ᶠ i:ℕ in atTop, ∃(stage:Realm G (e+1) Credit.leanC)(hm:stage.anchor=i),
        stage.draws=R.family.path.levels ∧ stage.paid=R.metals.O ∧ stage.y=zz R.family.path.levels ∧
        FundedMarkedWindingWindow.ReceiptOn R {(0:Fin 1)} {(0:Fin 1)} 0 dims k e j r d c q t w σ i stage hm.le:=by
  obtain ⟨fund,σ,t,hs,wide,menu,paid⟩:=FundedMarkedWindingWindow.pricedOnWithRate
    (J:={(0:Fin 1)}) (Z:={(0:Fin 1)}) le_rfl 0 (Finset.mem_singleton_self 0) dims k e j r grade w hw d
  refine ⟨fund,σ,t,hs,wide,menu,?_⟩
  intro R simple readout funded c q
  filter_upwards [paid R simple readout c q,FundedMarkedCoverRows.realm R simple fund funded 1
    (fun _=>0) (fun _=>1) (fun _=>Nat.zero_lt_one) e 1 0] with i receipt selected
  obtain ⟨stage,draws,metal,pace,anchor,_,_,_,reserves⟩:=selected
  obtain ⟨_,_,bill⟩:=reserves i le_rfl anchor.le
  exact ⟨stage,anchor,draws,metal,pace,receipt stage anchor.le pace bill⟩
end YM.Integration.WilsonOriginalQWindingAppointment
