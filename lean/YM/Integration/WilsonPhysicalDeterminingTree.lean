import YM.Integration.WilsonPhysicalDeterminingVertex

/-! The finite determining roster of an ordinary tree, with one common comparison order and fixed public prescription. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonPhysicalDeterminingTree
open Trace.Terrace WilsonMSDictionaryVector
open RG12 YM.Integration.WilsonLimitConstruction WilsonOrdinaryNestedBasis
open WilsonOrdinaryNestedSmoothTree WilsonOrdinaryNestedEnrollment
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom OPE.Nesting.Composite
open PhysMS Trace.Pilot RG17 Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater
open WilsonOrdinaryNestedTariff WilsonCenteredNestedViewer
open FVA2 FVA2.Register FVA2.Scale WilsonCenteredNestedProgram WilsonCenteredNestedGross
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open MeasureTheory
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z



variable {T:Campaign R}{W:Campaign.Pillars R T}{κ:ℝ}


/-- A vertex uses its arity, the grade of each child, and a retained output grade. -/
abbrev Request := (n : ℕ) × ((Fin n → ℕ) × ℕ)

def requests : (t : Tree) → (t.Leaf → S.Tag) → (t.Inner → ℕ) → ℕ → Finset Request
  | bud, _, _, _ => ∅
  | fork n arm, v, D, H =>
    (Finset.univ.biUnion fun sel : Branches F Q (f:=arm) (rollCaps D) =>
      Finset.univ.image fun m : Fin (H+1) => (⟨n, degrees (echoTags F Q v sel), m.val⟩ : Request)) ∪
    Finset.univ.biUnion fun i => requests (arm i) (childWages i v) (childAge i D) (rollCaps D i)

private theorem docket (U η : ℝ) (sep : 0 < η) (p q : ℕ)
    (t : Tree) (v : t.Leaf → S.Tag) (D : t.Inner → ℕ) (H : ℕ)
    (paid : ∀ k ∈ requests (Q:=Q) t v D H, Smooth (Q:=Q) (J:=J) Z M ν
      (region k.1 U η sep) p q k.2.2 k.2.1) :
    Docket (Q:=Q) (J:=J) Z M ν U η sep p q t v D H := by
  classical
  induction t generalizing H with
  | bud => trivial
  | fork n arm ih =>
    refine ⟨fun sel m => ?_, fun i => ?_⟩
    · apply paid (⟨n, degrees (echoTags F Q v sel), m.val⟩ : Request)
      exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨sel, Finset.mem_univ _, Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩⟩)
    · apply ih i
      intro k hk
      exact paid k (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hk⟩))

def Outcome (report : ℕ) {n : ℕ} (p : Fin n → Tree) (v : (fork n p).Leaf → S.Tag)
    (D : (fork n p).Inner → ℕ) (H : ℕ) {I : Type} [Fintype I] (ex : I → S.Tag)
    (U η ε δ : ℝ) (ηp : 0 < η) : Prop :=
    let level:=WilsonMeasuredWindow.stop R.family.path.levels simple report
    let shift:=fun (d:ℕ) (_:ℝ)=>LinearEquiv.refl ℂ (R.family.label d)
    let layout:=WilsonOriginalBlissObserved.layout F run.bliss J level shift
    layout.lens=(ℓ:Filter UVIndex) ∧ LogTrace F Q.port ∧
    let needed := requests (Q:=Q) (fork n p) v D H
    ∃ W j B, 0 ≤ B ∧ ∀ P : ℕ, ∃ least : ℕ, ∀ q ≥ least,
    ∃ panel : (k : ↥needed) → Panel R k.val.2.1 k.val.2.2,
    (∀ k c, ∃ a e, ∀ᶠ r in trail, 0 < r/((θ r)^(panel k).rise)^2 ∧
      wage F J Z layout (axes (R:=R) k.val.2.1 c) a e r ((panel k).labels c r)) ∧
    ((∀ k, WilsonPhysicalDeterminingVertex.Paid F J Z layout (region k.val.1 U η ηp) (P+W) q (panel k)) →
    ∃ C:ℝ,0≤C ∧ ∃ b:Fin (H+1)→ℝ, (∀ k,0≤b k) ∧
    ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (s:(fork n p).Inner→ℝ) (z:(fork n p).Plot),Accept r U η s z →
      let V:= program F Q J Z M ν q
      (∀ (k:Fin (H+1)) (c:Q.channels k),
        ‖Kernel.output F Q z v c - WilsonCenteredNestedProgram.run F Q V θ (fork n p) s z v D k ⟨Fin.last k.val,c⟩‖ ≤
          price F Q v D k ε j (B+C) s θ P) ∧
      ∀ (y:I→E4),Buffer z y δ → ∀ view:Viewers F,
        ‖whole (spectator F view) (Tree.profile z) (voices v) y (voices ex) -
          predicted F Q V θ v ex H D s z y view‖ ≤
          footprint v s (H+1)*ratiosLoss s ε +
            ∑ k:Fin (H+1),∑ c:Q.channels k,price F Q v D k ε j (B+C) s θ P *
              (b k*‖Q.actor k c‖))

theorem on_scheme {σ : Prescription (Press.portDeck G)} {dial : Bool} (matched : Main.Match Z simple M σ dial) (fund:FundedOriginalProperties.{u} simple κ W)
    (pace:WilsonWindowReportingPace.Slow R.kit)(store:XSpace.Normalize.Store G)
    (report:ℕ)(live:0<report)(clock:Coupling G θ) {n:ℕ} (p:Fin n→Tree) (v:(fork n p).Leaf→S.Tag)
    (D:(fork n p).Inner→ℕ) (H:ℕ) {I:Type} [Fintype I] (ex:I→S.Tag)
    {U η ε δ:ℝ} (U0:0≤U) (ηp:0<η) (εp:0<ε) (δp:0<δ) :
    Outcome run Z M ν report p v D H ex U η ε δ ηp :=by
  classical
  unfold Outcome
  intro level shift layout
  obtain ⟨logged,Wage,j,B,bp,consume⟩ :=
    WilsonOrdinaryNestedSmoothTree.original run Z M ν matched clock p v D H ex U0 ηp εp δp
  let needed := requests (Q:=Q) (fork n p) v D H
  have all (n : ℕ) (d : Fin n → ℕ) (h : ℕ) :=
    WilsonPhysicalDeterminingVertex.original F J Z M ν matched fund pace store run report live clock d h U η ηp
  refine ⟨(all 0 Fin.elim0 0).1, logged, Wage, j, B, bp, ?_⟩
  intro P
  have select (k : ↥needed) := (all k.val.1 k.val.2.1 k.val.2.2).2
  choose E invite using select
  let cost (k : ↥needed) := (P+Wage) + (P+Wage+E k+1)*(2*k.val.2.2+1)
  refine ⟨Finset.univ.sup cost, ?_⟩
  intro q room
  have atVertex (k : ↥needed) :=
    invite k (P+Wage) q ((Finset.le_sup (f:=cost) (Finset.mem_univ k)).trans room)
  choose panel paid using atVertex
  refine ⟨panel, fun k => (paid k).2.1, ?_⟩
  intro received
  apply consume P q
  apply docket Z M ν U η ηp (P+Wage) q
  intro k member
  exact (paid ⟨k,member⟩).2.2 (received ⟨k,member⟩)

theorem original (dial:Bool) (fund:FundedOriginalProperties.{u} simple κ W)
    (pace:WilsonWindowReportingPace.Slow R.kit)(store:XSpace.Normalize.Store G)
    (report:ℕ)(live:0<report)(clock:Coupling G θ) {n:ℕ} (p:Fin n→Tree) (v:(fork n p).Leaf→S.Tag)
    (D:(fork n p).Inner→ℕ) (H:ℕ) {I:Type} [Fintype I] (ex:I→S.Tag)
    {U η ε δ:ℝ} (U0:0≤U) (ηp:0<η) (εp:0<ε) (δp:0<δ) :
    Outcome run Z M ν report p v D H ex U η ε δ ηp := by
  obtain ⟨σ,matched⟩ := Main.wilson_to_MS Z simple M dial
  exact on_scheme run Z M ν matched fund pace store report live clock p v D H ex U0 ηp εp δp

end YM.Integration.WilsonPhysicalDeterminingTree
