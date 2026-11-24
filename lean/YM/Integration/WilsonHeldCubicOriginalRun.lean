import YM.Integration.WilsonHeldCubicElection
import YM.Integration.WilsonGaussianDeterminantTender

/-! On the original elected run the integrated cubic error, the whole marked
height estimate, and the independent determinant estimate use one Cash. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonHeldCubicOriginalRun
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (R : Run G)
local notation "joined" => WilsonGaussianDeterminantTender.joined G J χ
  ((WilsonHeldCubicElection.decal G χ).paired δ)

def On (paid : QLocalRequestedSectorCalendar.Paid J joined extra γ R.kit) : Prop :=
    ∀ {Γ : Census V} (A : NumericSchedule R.family J), ∀ᶠ m : ℕ in atTop,
      ∀ (d : LocalFormal.Datum R.family Γ), d.level=m → ∀ (F : AnalyticInput J A d) {η : ℝ}
      (I : FullPreparedInputAt F η), Retained.NativeIntake I →
      let lev := R.alloy.B.a
      let i := lev.clock.J d.level
      let j := lev.clock.J (d.level+1)
      let S := lev.clock.op d.level d.period
      let Q := R.kit.target j i
      let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let b := paid.choose j i
      ∃ H : WilsonRootedSubmittedTail.CashAt I b,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
        Crossed J γ R A d b H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
        ManuscriptQLocalMarkedHeightRun.High (expense J Q) H J Γ ((2*g)^(J.order+1)) ∧
        ∀ n ≤ S.patch.J, ∀ k ≤ S.patch.J, WilsonHeldCubicElection.Bought H χ n k ∧
          ∀ h ≤ S.patch.J, WilsonGaussianDeterminantStage.Bought χ H n k h

theorem original (paid : QLocalRequestedSectorCalendar.Paid J joined extra γ R.kit) (simple : G.Simple) :
    On J χ δ extra γ R paid := by
  intro Γ A
  have source := WilsonGaussianDeterminantTender.opens R J χ ((WilsonHeldCubicElection.decal G χ).paired δ)
    extra γ paid simple (Γ:=Γ) A
  filter_upwards [source] with m ready d hm F η I admitted
  obtain ⟨H,res,cross,high,_,_,_,_,_,⟨cost,_⟩,_,det⟩ := ready d hm F I admitted
  refine ⟨H,res,cross,high,fun n hn k hk => ⟨?_,det n hn k hk⟩⟩
  exact cost n hn k hk _ _ _ _ _ _ H (protocol (n:=d.period) R.alloy.B d.below R.kit.pledging.conducts.full)

end YM.Integration.WilsonHeldCubicOriginalRun
