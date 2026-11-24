import YM.Integration.WilsonOriginalRawQWindingVisit

/-! Sum the true winding invoices of the four real readings of each native registered Wilson row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalRawQWindingLedger
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

def listing : Source D u ≃ (Bool × Bool) × ((j:V) × Count D u j) where
  toFun a:=⟨a.2.2,a.1.1.1,index R i per D u a⟩
  invFun raw:=by
    obtain ⟨b,⟨j,⟨⟨s,hs⟩,t⟩⟩⟩:=raw
    subst j
    exact ⟨s,t,b⟩
  left_inv a:=by rcases a with ⟨s,t,b⟩; rfl
  right_inv raw:=by rcases raw with ⟨b,j,⟨s,hs⟩,t⟩;subst j;rfl

def invoice (k:V→ℕ)(cap:ℕ)(w:ℝ)(b:Bool):ℝ :=
  bill (chosen Q D u μ orders unit (fun _ : V=>b)) (grades R i per D u k) cap w

def share (k:V→ℕ)(cap:ℕ)(w:ℝ)(a:Source D u):ℝ :=
  charge (enrolled R i per Q D u μ orders a) (grades R i per D u k) cap w a.1.1.1 (index R i per D u a)

theorem total (k:V→ℕ)(cap:ℕ)(w:ℝ):
    ∑a,share R i per Q D u μ orders k cap w a=2*∑b:Bool,invoice R i per Q D u μ orders k cap w b:=by
  let leaf (b:Bool × Bool)(y:((j:V) × Count D u j)) :=
    charge (chosen Q D u μ orders unit (fun _ : V=>b.1)) (grades R i per D u k) cap w y.1 y.2
  let chi (b:Bool):=invoice R i per Q D u μ orders k cap w b
  calc
    _ = ∑p : (Bool × Bool) × ((j:V) × Count D u j), leaf p.1 p.2 :=
      (listing R i per D u).sum_comp (fun p=>leaf p.1 p.2)
    _ = ∑p : Bool × Bool,chi p.1 :=by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b _
      rw [Fintype.sum_sigma]
      rfl
    _ = 2*∑b:Bool,chi b :=by simp only [Fintype.sum_prod_type,Fintype.sum_bool];ring

theorem weighted (k:V→ℕ)(cap:ℕ)(w:ℝ)(v:V)
    (band:|Pert.Asymptotics.regulatorRun R.family N per (i+1)| ≤ 1) :
    ∑a,‖weight D u N ((Stock.census V).fire v) a‖*share R i per Q D u μ orders k cap w a ≤
      2*∑b:Bool,invoice R i per Q D u μ orders k cap w b :=by
  rw [←total R i per Q D u μ orders k cap w]
  apply Finset.sum_le_sum
  intro a _
  have ph:(h:Bool)→‖FundedOriginalMarkedInput.phase h‖=1:=by intro h;cases h <;> simp [FundedOriginalMarkedInput.phase]
  have cm:‖SignedOpeningMarkedVertices.multiplier D u ((Stock.census V).fire v) a‖ ≤ 1:=by
    unfold SignedOpeningMarkedVertices.multiplier
    split <;> simp [ph]
  have amp:‖weight D u N ((Stock.census V).fire v) a‖ ≤ 1:=by
    rw [WilsonOriginalChargedRawJet.weight,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    exact mul_le_one₀ cm (by positivity) (pow_le_one₀ (abs_nonneg _) band)
  have np:0 ≤ share R i per Q D u μ orders k cap w a:=by
    unfold share charge
    exact Finset.sum_nonneg fun _ _=>abs_nonneg _
  exact mul_le_of_le_one_left np amp

end YM.Integration.WilsonOriginalRawQWindingLedger
