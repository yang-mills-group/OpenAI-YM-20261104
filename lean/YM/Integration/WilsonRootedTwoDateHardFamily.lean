import YM.Integration.WilsonRootedTwoDateHardSource
import YM.Integration.WilsonRootedTwoDateIndependentHard
import YM.Integration.WilsonRootedTwoDateForcedRegistration

/-! The old ambient test and fresh packet test may be chosen independently after one common compulsory tape. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardFamily
open RG3.Script.Picnic
open Function Finset Lattice Wilson RG Marker Overlay Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep Comparison.Density.RenderM
open WilsonLimitConstruction.FundedMarkedFieldSplit WilsonLimitConstruction.FundedSpringJoinedAddresses
open QLocalCompulsoryJoinedTape QLocalMarkedJoinedCatalogue QLocalMarkedJoinedLinear
open QLocalThermalPacketDivision WilsonRootedTwoDateProduct Pert.Asymptotics
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
variable (oldD : V→ ComparisonDensity.Address.Orbit) (b : Overlay.Bands (Stock.census V) (R.family.path.rep N p (m+1)))
local notation "Pair" => TestSpace oldD × TestSpace (D)

/-- The supported signed hard insertion is preselected jointly over both external test spaces. -/
def Enrolled : Prop :=
    let T := WilsonRootedTwoDateIndependentHard.before fresh oldD b
    let H := ActualOriginalQInitialInput.paid R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
    let hg := (IterationFour.Currency.g_pos R.makes N p (m+1) fresh.below).ne'
    let K := OriginalForcedAddresses.actual_keeper R hG N (m+1) p fresh.below
    ∃L : QLocalFixedJoinedFamily.Fixed K T (WilsonRootedTwoDateHardSource.source (Q:=(X)) (P₀) oldD H hg (1:ℂ)),
      FunctionalRetains (replace T L.book) (fun v=>{fresh.roots v}) ∧
      (∀z : Pair,((replace T L.book).leaf z).Active ∧ Financed ((replace T L.book).menu.terms z) ∧ ∀U,
        ((replace T L.book).leaf z).contents.cluster U=Poly.pass (dirty (P₀) (X).p z.2 (g) U)*((WilsonOriginalPointTaste.representation oldD b).leaf z.1).contents.cluster U ∧
        ((replace T L.book).leaf z).density U=Poly.pass (dirty (P₀) (X).p z.2 (g) U)*((WilsonOriginalPointTaste.representation oldD b).leaf z.1).density U) ∧
      ∀(oldTest : TestSpace oldD) (freshTest : IndependentTests (D)) U,
        ((replace T L.book).leaf (oldTest,testInclusion (D) freshTest)).density U=
          Poly.pass ((P₀).read (testInclusion (D) freshTest) (g) U-ManuscriptQLocalOriginalConditionalTail.source (P₀) (X).p (g) freshTest 1 U)*((WilsonOriginalPointTaste.representation oldD b).leaf oldTest).density U

theorem original (roots : b.origins=fresh.roots) (active : b.Active) {w : V→ℝ} {u c d t : ℝ}
    (radial : b.Radial w u c d t) :
    Enrolled fresh hG oldD b := by
  unfold Enrolled
  dsimp only
  let T := WilsonRootedTwoDateIndependentHard.before fresh oldD b
  let addr := fun v=>({fresh.roots v}:Support (R.family.side (m+1) p))
  let K := OriginalForcedAddresses.actual_keeper R hG N (m+1) p fresh.below
  have H := ActualOriginalQInitialInput.paid R hG fresh.labels fresh.request fresh.schedule fresh.datum fresh.prescription fresh.roots fresh.scale fresh.degree
  have hg := (IterationFour.Currency.g_pos R.makes N p (m+1) fresh.below).ne'
  have held₀ : FunctionalRetains (WilsonOriginalPointTaste.representation oldD b) addr := by simpa only [addr,roots] using WilsonOriginalPointTaste.retains oldD b active
  have held : FunctionalRetains T addr := {
    origins := held₀.origins
    regular i v nz hv := by obtain ⟨z,U,nz⟩ := nz;exact held₀.regular i v ⟨z.1,U,nz⟩ hv
    forced i j v nz hv := by obtain ⟨z,U,nz⟩ := nz;exact held₀.forced i j v ⟨z.1,U,nz⟩ hv
    captions i v nz hv := by obtain ⟨z,nz⟩ := nz;exact held₀.captions i v ⟨z.1,nz⟩ hv }
  let F := WilsonRootedTwoDateHardSource.source (Q:=(X)) (P₀) oldD H hg (1:ℂ)
  let Keeps (A : Pair→Overlay.Bands (Γ) (X)) (_ : ℕ) := ∀z,(A z).origins=b.origins ∧ (A z).Active ∧ Held addr (A z)
  have start : Keeps T.menu.terms 0 := fun z=>⟨T.root,(WilsonOriginalPointTaste.active oldD b active z.1).articles,prior addr T held z⟩
  have fund (z : Pair) : Financed (T.menu.terms z) := by
    obtain ⟨tags,pack,_⟩ := WilsonOriginalPointTaste.ambient_series oldD b active radial (good) z.1
    exact ⟨tags,pack⟩
  have advance (A : Pair→Overlay.Bands (Γ) (X)) (j : ℕ) (_ : j<Fintype.card (Γ).Mode) (ok : Keeps A j)
      (funds : ∀z,Financed (A z)) (s : (Γ).Mode) (_ : s≠(Γ).quiet) :
      Keeps (fun z=>bands (A z) (addition (Y:=plot (P₀)) K (A z) s (F.field s z))) (j+1) := by
    intro z
    have law := QLocalThermalJoinedLaw.charged (Q:=(X)) (P₀) H b.origins held.origins s z.2 (1:ℂ)
    have allow := QLocalMarkedJoinedEligibility.issued K (A z) (ok z).2.1 (good).forced (funds z).1 s (F.field s z) ((ok z).1.symm ▸ law)
    exact ⟨(ok z).1,QLocalCompulsoryJoinedTape.active _ (ok z).2.1 _ allow,
      WilsonLimitConstruction.FundedSpringJoinedAddresses.next addr K (A z) (ok z).2.2 s (F.field s z) (token addr (P₀) H 1 (X).p s z.2)⟩
  have quiet (z : Pair) U : ((1:ℂ) • dirty (P₀) (X).p z.2 (g) U).part (Γ).quiet=0 := by
    rw [Poly.part_smul,QLocalThermalPacketDivision.dirty,QLocalThermalPacketDivision.part,(WilsonPrescribedPacketTail.slice (P₀) _).quiet_read,mul_zero]
  obtain ⟨L⟩ := QLocalFixedJoinedFamily.sale K T F quiet fund
  have ok := L.preserves Keeps start advance
  have full := L.field
  simp only [one_smul] at full
  refine ⟨L,restored addr T held L.book (fun z=>(ok z).2.2),fun z=>⟨⟨(ok z).2.1,(WilsonOriginalPointTaste.active oldD b active z.1).captions⟩,full z⟩,?_⟩
  intro x y U
  exact (((full (x,testInclusion (D) y)).2 U).2).trans (congrArg (fun v=>Poly.pass v *
    ((WilsonOriginalPointTaste.representation oldD b).leaf x).density U)
    (WilsonRootedTwoDateFreshMask.dirty_source (P₀) (X).p H hg y U))

end YM.Integration.WilsonRootedTwoDateHardFamily
