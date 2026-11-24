import YM.Integration.WilsonOriginalProjectedCurvatureLamps
import YM.Integration.WilsonOriginalProjectedCurvatureClock

/-! The rooted offers, issued ranks and complete original mode wages needed
from the registered point roster in the original Earn.Scene.Armada. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureProduction
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureCredits
open WilsonOriginalProjectedCurvaturePassport
open scoped Classical BigOperators
variable {G : Gauge} {B : MS.Local.Physical.Deck G}
  {V : Type} [DecidableEq V] [Fintype V] (R : Run G) (J : Request V)
  (Q : MS.Land.Prescription B) (u : V → MS.Rake.Label B)
  (μ σ : ℝ) (extra : V → ℕ) (w : V → ℝ) (K : ℕ)
local notation "D₁" => ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _ => 0)
local notation "t" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) u

theorem census (c : (Stock.census V).Mode) : c.val.card ≤ Fintype.card V ∧
    (∑ _ ∈ c.val, t) ≤ Fintype.card V * t := by
  have h := Finset.card_le_univ c.val
  refine ⟨h,?_⟩
  simpa only [Finset.sum_const, Nat.nsmul_eq_mul] using Nat.mul_le_mul_right t h

theorem original (hw : ∀i,0<w i) :
    ∃C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ (N p L : ℕ) (o : V → Site (R.family.side L p)) (orders : V→ℕ),
    (∀i,orders i≤K) → L≤N → 0<Pert.Asymptotics.regulatorRun R.family N p L →
    Pert.Asymptotics.regulatorRun R.family N p L≤1 →
    let D := ActualOriginalQPointSetup.pointDatum R J p L o
    let η := μ-R.family.S.scale N
    let X := WilsonOriginalProjectedCurvatureLamps.cohort Q D u η orders N σ extra
    QuadraticLocal.Earn.Offers X w σ ((C*(1+‖R.family.S.scale N‖)^b)*
        WilsonOriginalProjectedCurvatureClock.charge R J u σ σ extra w) ∧
      QuadraticLocal.Earn.Issues X σ (ActualOriginalQLayout.rankCap R u) (fun _ => t) ∧
      (∀i,(X i).Budget) ∧
      (∀c:(Stock.census V).Mode, c.val.card ≤ Fintype.card V ∧
        (∑ _ ∈ c.val, t) ≤ Fintype.card V * t) := by
  obtain ⟨C,hC,b,h⟩ := WilsonOriginalProjectedCurvatureClock.quoted R J Q u μ σ σ extra w K hw
  refine ⟨C,hC,b,?_⟩
  intro N p L o orders ho hL hg hup
  let D := ActualOriginalQPointSetup.pointDatum R J p L o
  let η := μ-R.family.S.scale N
  refine ⟨?_,WilsonOriginalProjectedCurvatureLamps.issued Q D u η orders N σ extra,?_,census R u⟩
  · intro x
    have q := WilsonOriginalProjectedCurvatureLamps.offers Q D u η orders N σ σ extra w hL hg hup hw x
    have he := WilsonOriginalProjectedCurvaturePointCredit.same R J Q u p L o η orders σ σ extra w
    exact ⟨q.1,q.2.1,q.2.2.trans (he.le.trans (h N orders ho))⟩
  · intro i
    exact (WilsonOriginalProjectedCurvatureRender.priced Q D u η orders N i.1 σ (extra i.1.1.1) i.2).1

end YM.Integration.WilsonOriginalProjectedCurvatureProduction
