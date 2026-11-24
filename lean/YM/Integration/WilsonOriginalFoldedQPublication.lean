import YM.Integration.WilsonOriginalSignedQWinding
import YM.Integration.WilsonOriginalQWindingAppointment

/-! The full original finite reading and the signed rooted seam on the same elected nonbare source and normalizer. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFoldedQPublication
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
open WilsonOriginalEarnedUnaryRaw (payer)
open WilsonVacuumPreResetTorusDeposit (bank)
open WilsonVacuumPreResetDatedCourse (coin)
local notation "F₀" => repeatF (step R i per)
local notation "C" => Stock.census V
local notation "P₀" => ActualOriginalQPackets.packets Q D u μ orders N
local notation "K" => model R N i per hi
local notation "B₁" => (fun B₀=>Stationary.arm G (coarse R i per) 1 B₀)

structure IssuedPage (π:ℕ→Layout G) (k:V→ℕ) (j r:ℕ) (stage:Realm G (e+1) Credit.leanC)
    (anchor:stage.anchor ≤ i) (w σ:Gear G→ℝ) (c q t:ℕ) (colour:G.ColorIndex) (choice:Tags R):Prop where
  finite : ∀(tag:(step R i per).Choices)(B₀:Stationary.Link G (coarse R i per))(l:ℕ), l≤e+2 →
    let W:=payer R N i per hi Q D u μ orders x F₀ v B₀ l
    let I₀:=NativePaidPacketColors.colors P₀ (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x
    let actual:=Bulk.Fk K F₀ tag I₀ (B₁ B₀) l
    let outside:=WilsonOriginalSingleMarkedRegister.token C l W.source*
      (∑a,W.amplitude a • register C l (OriginalRadialSeries.observed W.B (readout R N i per Q D u μ orders x colour choice a)))
    ratio actual=1+outside ∧ logMarked actual=outside

  source : ∀a:Source D u,
    let s:=a.1.1.1
    let T:=data (R:=R) (i:=i) (per:=per) Q D u μ orders x a
    let n₀:=coarse R i per
    let fee:=ratioHigh stage.draws stage.paid N i
    let H:=WilsonMarkedIndependentFoldedIntegral.folded R N i (gr k s) T.1 n₀
    let Y:=picked (full a) s (idx a)
    pPly (view a) {s} (coilH stage.draws stage.paid i N n₀ (IndependentSourcePathFamily.independent Y points) (gr k) fee {s})=Blue.mix fee H ∧
      flash H=readout R N i per Q D u μ orders x colour choice a
  winding :
    let gear:=(stage.mint i anchor).gear
    let width:=4*max (w gear) (stage.mint (i+1) (by omega)).σ
    let rent:=2*∑b:Bool,invoice R i per Q D u μ orders k e width b
    let tail:=Real.exp (-(σ gear/512)*((R.family.side i per).val:ℝ))
    ∀z:Source D u→ℂ,
      (∀a:Source D u,heard {a.1.1.1} a.1.1.1 r (windingRow R N i per Q D u μ orders k j r stage a) (z a)) →
      ‖∑a,amps a*z a‖*g₁^(-(c:ℝ)) ≤ g₁^q*rent ∧
        ‖∑a,amps a*z a‖ ≤ (admittedCost R.family.path.levels i)^t*(tail*rent)

theorem original (k:V→ℕ)(j r:ℕ)(stage:Realm G (e+1) Credit.leanC)(anchor:stage.anchor ≤ i)
    {w σ:Gear G→ℝ}(hw:∀a,0<w a)(hs:0≤σ (stage.mint i anchor).gear)
    (draws:stage.draws=R.family.path.levels)(metal:stage.paid=R.metals.O)
    (ready:FundedMarkedWindingWindow.ReceiptOn R {v} {v} v (OrbitD D) (gr k) e j r d c q t w σ i stage anchor)
    (simple:G.Simple)(fund:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices fund R.kit)
    (colour:G.ColorIndex)(choice:Tags R)(band:|g₁|≤1)
    {m:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){μ₀ debt:ℝ}
    (issued:Issued R N (i+1) e (Z (i+1)) μ₀ debt):
    IssuedPage R N i per hi Q D u μ orders x v π k j r stage anchor w σ c q t colour choice:=by
  refine ⟨?_,?_,?_⟩
  · intro tag B l hl
    exact WilsonOriginalEarnedReefUnary.original R N i per hi Q D u μ orders x tag v colour choice simple fund rows course lo issued B l hl
  · intro a
    have ha:a.1.1.1=v:=Subsingleton.elim .. 
    have ri:FundedMarkedWindingWindow.ReceiptOn R {a.1.1.1} {a.1.1.1} a.1.1.1 (OrbitD D) (gr k) e j r d c q t w σ i stage anchor:=by rw [ha];exact ready
    have got:=WilsonOriginalRawQWindingVisit.original R N i per hi Q D u μ orders x a k j r stage anchor hw ri simple fund rows colour choice (ratioHigh stage.draws stage.paid N i)
    have equal:=got.2.2
    dsimp only at equal ⊢
    simpa only [draws,metal] using equal
  · exact WilsonOriginalSignedQWinding.original R N i per hi Q D u μ orders x v k j r stage anchor hw hs ready simple fund rows colour choice band
end YM.Integration.WilsonOriginalFoldedQPublication
