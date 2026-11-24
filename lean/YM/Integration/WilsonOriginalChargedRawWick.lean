import YM.Integration.WilsonOriginalChargedForestQ
import YM.Integration.WilsonOriginalChargedRawJet

/-! The original raw Laurent Q, with each source row restored, on the purchased physical Wick forest. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalChargedRawWick
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

include hi in
private theorem legal : Bulk.Well Y :=by
  have H:=ActualOriginalQPackets.packets_paid Q D u μ orders N ((levels R).budget (i + 1))
    (fun _=>1) 1 zero_lt_one (fun _=>zero_lt_one)
  have law:=(Bulk.Colors.no_hole G (R.family.side (i + 1) per) C).1
  exact NativePaidPacketColors.colors_well H (ActualRunKernelPackets.regulator_pos R N per (i+1) hi).ne' v₀ law.suppose_vac law.natural law.envelope _

variable (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)(B:fieldDir G (coarse R i per) 1)
variable (z:Precision.Key F G→ℝ)
local notation "M" => saddle R N i per F

open WilsonOriginalChargedForestQ WilsonVacuumPreResetDepositedIntegrand
open WilsonVacuumPreResetDatedDeposit (Issued)

open SignedOpeningMarkedVertices WilsonOriginalChargedRawRoster
open WilsonOriginalChargedRawJet (weight)
local notation "unit" => (fun _ : V => (1:ℂ))

def charged (d:ℕ)(J:(C).Mode) : MvPolynomial (Precision.Key F G) ℂ :=
  ∑ a:Source D u, weight D u N J a • SignedRegisteredMarkedProgram.register F B
    (coeff (d+debt D (u:=u) a.1) (supplied Q D u μ orders unit K F M x a))

def atoms (Z:SeriesA G)(r:ℕ)(s:Hot (Board C r)) : MvPolynomial (Precision.Key F G) ℂ :=
  let d := (Join.right s.val).val.card
  (d.factorial:ℂ) • if (Join.left s.val).val.Nonempty then
    charged R N i per hi Q D u μ orders x F B d (Join.left s.val)
  else SignedRegisteredMarkedProgram.register F B (coeff d (opened R N i per hi F Z))

theorem forest (Z:SeriesA G)(e r:ℕ){σ cash:ℝ}
    (bank:Issued R N (i + 1) e Z σ cash) :
    WilsonVacuumPreResetDepositedIntegrand.family R N i per hi F tag Z Y (e + 2) B r =
      atoms R N i per hi Q D u μ orders x F B Z r := by
  funext s
  unfold WilsonVacuumPreResetDepositedIntegrand.family Assembly.generator atoms
  dsimp only []
  by_cases hc:(Join.left s.val).val.Nonempty
  · simp only [dif_pos hc,if_pos hc]
    apply congrArg (fun p:MvPolynomial (Precision.Key F G) ℂ => ((Join.right s.val).val.card.factorial:ℂ) • p)
    apply Valence.Enlist.paint_inj
    intro y
    unfold charged
    simp only [_root_.map_sum,_root_.map_smul,smul_eq_mul,SignedRegisteredMarkedProgram.reading]
    have good:=(model R N i per hi).hessian_pos F tag
    rw [OriginalMarkedHeatCovariance.precision R N i per hi F tag] at good
    have hM:M=reveal G S F*((reveal G S F).transpose*M):=by
      apply sweeps G S F (prediction R N i per) (lower R N i) (isUnit_iff_ne_zero.mpr good.det_pos.ne')
      exact horizon_step (levels R) i N hi _ _ (step R i per).sizes
    exact WilsonOriginalChargedRawJet.kernel Q D u μ orders K F M N hi
      v₀ x ⟨Join.left s.val,hc⟩ B y (Join.right s.val).val.card hM
  · simp only [dif_neg hc,if_neg hc]
    apply congrArg (fun p:MvPolynomial (Precision.Key F G) ℂ => ((Join.right s.val).val.card.factorial:ℂ) • p)
    apply Valence.Enlist.paint_inj
    intro y
    rw [SignedRegisteredMarkedProgram.reading,same_axes R i per F B y]
    exact WilsonVacuumPreResetDepositedLetters.original R N i per hi F tag Z Y
      ((levels R).budget (i + 1)) (e + 2) bank.positive bank.purchase bank.lower
      (fun a ha=>by have h:=bank.upper a ha;omega) B y (legal R N i per hi Q D u μ orders x) _

theorem original {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}
    (bank:Issued R N (i + 1) e (Z (i + 1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(l:ℕ)(hl:l ≤ e + 2)(s:(Board C l).Mode) :
    let B:=Stationary.arm G _ 1 B₀
    (Bulk.Fk K F tag (QuadraticLocal.Fk.grant (π (i + 1)) (Step.tape (e + 2)) Y) B l).part s =
      (Cloud.prescription ((model R N i per hi).covariance F tag)
        ((model R N i per hi).symm F tag) 0
        (atoms R N i per hi Q D u μ orders x F B (Z (i + 1)) l)).part s := by
  intro B
  rw [←forest R N i per hi Q D u μ orders x F tag B _ e l bank]
  exact (course.filed i lo hi per F tag Y (legal R N i per hi Q D u μ orders x) B₀ l hl s).trans
    (WilsonOriginalOccupiedForestIntegral.integrated R N i per hi F tag _ Y ((levels R).budget (i + 1))
      (e + 2) bank.positive bank.purchase bank.lower (fun a ha=>by have h:=bank.upper a ha;omega)
      B l (legal R N i per hi Q D u μ orders x) s).symm

/-- Grant changes precisely the vacuum entry.  This permits the very same statement on the actual paid pupil. -/
theorem deposited {m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}
    (bank:Issued R N (i + 1) e (Z (i + 1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(l:ℕ)(hl:l ≤ e + 2)(s:(Board C l).Mode) :
    let B:=Stationary.arm G _ 1 B₀
    let raw:=NativePaidPacketColors.colors P (QuadraticLocal.Fk.money (π (i+1)) (Step.tape (e+2))) x
    (Bulk.Fk K F tag raw B l).part s =
      (Cloud.prescription ((model R N i per hi).covariance F tag)
        ((model R N i per hi).symm F tag) 0
        (atoms R N i per hi Q D u μ orders x F B (Z (i + 1)) l)).part s :=
  original R N i per hi Q D u μ orders x F tag course lo bank B₀ l hl s

end YM.Integration.WilsonOriginalChargedRawWick
