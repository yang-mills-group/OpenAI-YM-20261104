import YM.Integration.WilsonLimitConstruction.FundedSpringJoinedAddresses
import YM.Integration.OriginalForcedAddresses
import YM.Integration.WilsonOriginalPointSeries
import YM.Integration.WilsonRootedTwoDateFreshMask

/-! The original compulsory catalogue receives the fresh flagged point packet on its actual carrier. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateForcedRegistration
open Function Finset Lattice Wilson RG Marker Overlay Precision OPE.Therm
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open MergeProof MergeProof.Accent Comparison.Density.RenderM WilsonLimitConstruction.FundedMarkedFieldSplit
open QLocalMarkedJoinedCatalogue WilsonRootedTwoDateProduct Pert.Asymptotics
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ}
variable (fresh : Seed R B V N p m) (hG : G.Simple)
local notation "X" => R.family.path.rep N p (m+1)
local notation "Γ" => Stock.census V
local notation "D" => (ActualOriginalQPointSetup.request R fresh.labels fresh.request).tests
local notation "g" => regulatorRun R.family N p (m+1)
local notation "P₀" => ActualOriginalQInitialInput.packets R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
local notation "good" => (R.makes.wilson.represents N p (m+1) fresh.below).good.labels
variable (b : Overlay.Bands (Stock.census V) (R.family.path.rep N p (m+1)))

/-- The attachment precedes the smooth test and the field. Every cut continues to use the original Wilson flag register. -/
def Registered : Prop :=
    ∃A : Compulsory (TestSpace (D)) (Γ) G (R.family.side (m+1) p),
      FunctionalRetains (replace (WilsonOriginalPointTaste.representation (D) b) A) (fun v=>{fresh.roots v}) ∧
      Multilinear (D) (replace (WilsonOriginalPointTaste.representation (D) b) A) ∧
      (∀x,((replace (WilsonOriginalPointTaste.representation (D) b) A).leaf x).Active ∧ Financed ((replace (WilsonOriginalPointTaste.representation (D) b) A).menu.terms x) ∧ ∀U,
        ((replace (WilsonOriginalPointTaste.representation (D) b) A).leaf x).contents.cluster U=Poly.pass (QLocalThermalPacketDivision.dirty (P₀) (X).p x (g) U)*((WilsonOriginalPointTaste.representation (D) b).leaf x).contents.cluster U ∧
        ((replace (WilsonOriginalPointTaste.representation (D) b) A).leaf x).density U=Poly.pass (QLocalThermalPacketDivision.dirty (P₀) (X).p x (g) U)*((WilsonOriginalPointTaste.representation (D) b).leaf x).density U) ∧
      ∀(y : IndependentTests (D)) U,((replace (WilsonOriginalPointTaste.representation (D) b) A).leaf (testInclusion (D) y)).density U=
        Poly.pass ((P₀).read (testInclusion (D) y) (g) U-ManuscriptQLocalOriginalConditionalTail.source (P₀) (X).p (g) y 1 U)*((WilsonOriginalPointTaste.representation (D) b).leaf (testInclusion (D) y)).density U

theorem current (roots : b.origins=fresh.roots) (active : b.Active) {w : V→ℝ} {u c d t : ℝ}
    (radial : b.Radial w u c d t) :
    Registered fresh hG b := by
  unfold Registered
  have H := ActualOriginalQInitialInput.paid R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
  have hg := (IterationFour.Currency.g_pos R.makes N p (m+1) fresh.below).ne'
  have held : FunctionalRetains (WilsonOriginalPointTaste.representation (D) b) (fun v=>{fresh.roots v}) := by
    simpa only [roots] using WilsonOriginalPointTaste.retains (D) b active
  have prior (x : TestSpace (D)) : Financed ((WilsonOriginalPointTaste.representation (D) b).menu.terms x) := by
    obtain ⟨tagged,packets,_⟩ := WilsonOriginalPointTaste.ambient_series (D) b active radial (good) x
    exact ⟨tagged,packets⟩
  obtain ⟨A,ret,linear,all⟩ := WilsonLimitConstruction.FundedSpringJoinedAddresses.registered (fun v=>{fresh.roots v}) (P₀)
    (OriginalForcedAddresses.actual_keeper R hG N (m+1) p fresh.below) H hg 1 (WilsonOriginalPointTaste.representation (D) b) held (good).forced
    (WilsonOriginalPointTaste.active (D) b active) prior
  simp only [one_smul] at all
  refine ⟨A,ret,linear (WilsonOriginalPointTaste.multilinear (D) b),all,?_⟩
  intro y U
  exact (((all (testInclusion (D) y)).2.2 U).2).trans (congrArg (fun v=>Poly.pass v *
    ((WilsonOriginalPointTaste.representation (D) b).leaf (testInclusion (D) y)).density U)
    (WilsonRootedTwoDateFreshMask.dirty_source (P₀) (X).p H hg y U))

end YM.Integration.WilsonRootedTwoDateForcedRegistration
