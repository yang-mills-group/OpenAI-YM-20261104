import YM.Integration.WilsonOrdinaryNestedDoses

/-! A single advance purchase on the true hierarchy suffices for the whole
separated nested MS reading. The extra coupling degree charged at every
ordinary vertex precedes both the perturbative order and all scale ratios. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedHierarchy
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom
open PhysMS Trace.Pilot WilsonCenteredNestedProgram WilsonOrdinaryNestedTariff WilsonCenteredNestedViewer
open Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater FVA2 FVA2.Register FVA2.Scale
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "θ" => reading F J Z

theorem original (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort)
    (clock:Coupling G θ) {n:ℕ} (p:Fin n→Tree) (v:(fork n p).Leaf→S.Tag)
    (D:(fork n p).Inner→ℕ) (H:ℕ) {I:Type} [Fintype I] (ex:I→S.Tag)
    {U η ε δ:ℝ} (U0:0≤U) (ηp:0<η) (εp:0<ε) (δp:0<δ) :
    LogTrace F Q.port ∧ ∃ W j B, 0≤B ∧ ∀ P q:ℕ,
    WilsonOrdinaryNestedDoses.Inventory (Q:=Q) (J:=J) Z M ν U η (P+W) q (fork n p) v D H →
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
              (b k*‖Q.actor k c‖) := by
  obtain ⟨sharp,j,B,Bp,read⟩:=WilsonOrdinaryNestedPublic.original Z M ν run clock p v D H ex U0 ηp εp δp
  obtain ⟨W,rate⟩:=WilsonOrdinaryNestedDoses.original run Z M ν clock U η (fork n p) v D H
  exact ⟨sharp,W,j,B,Bp,fun P q paid=>read P q (rate W le_rfl P q paid)⟩

end YM.Integration.WilsonOrdinaryNestedHierarchy
