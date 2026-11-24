import YM.Integration.WilsonSharpPhysicalTreeDetectorSpectators
import YM.Integration.WilsonCenteredNestedElection

/-! The incumbent physical reader election, retaining its original filter and
matrix, with sharp spectators for every finite raw tree on that one witness. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonSharpPhysicalTreeDetectorApplication
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Log OPE.Arboreal
open PhysicalNext.Repeat.Legato Climb
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}

def AllTrees (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) : Prop :=
  ∀ (I J : Type) [Fintype I] [Fintype J] (s : Arboreal I) (p : I→C.book.Token) (h : ℕ)
    (d : (↑s.leaves : Type)→ℕ) (g : J→ℕ) (v : Labels S d) (w : Labels S g), crop p s.leaves = names v →
    ∀ (M η c : ℝ), 0 ≤ M → 0 < η → 0 < c →
    ∃ (k : ℕ) (A : ℝ), 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (x : I→E4) (t : I→ℝ) (y : J→E4),
      t s.root = r → s.Convoy M η t x → ClearOf (x s.root) y c →
      Injective (beside (crop x s.leaves) y) ∧ Injective (beside (sole (x s.root)) y) ∧
      ‖algebraError F Q (crop x s.leaves) (x s.root) v y w h‖ ≤ A * s.listPrice p t (h+1) k ∧
      ∀ q : Viewers F, ‖formula F Q (crop x s.leaves) (x s.root) v y w h q‖ ≤ A * s.listPrice p t (h+1) k

lemma same_reader (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (paid : Services C f S) (trace : LogTrace F Q.port) : AllTrees F Q := by
  intro I J _ _ s p h d g v w hp M η c hM hη hc
  exact WilsonSharpPhysicalTreeDetectorSpectators.with_geometry F Q paid trace s p h v w hp hM hη hc

theorem elected (R : Run G) (simple : G.Simple) {cohort : Ultrafilter (ℕ×ℕ) → Prop}
    (funded : WilsonMacroscopicFundedReader.Elected.{u} R simple cohort) (v : Extraction.Order) :
    ∃ (w : Extraction.Order) (S : Table R.family.book) (F : Final R.family (v.refine w) S)
      (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (l : Ultrafilter (ℕ×ℕ)),
      Facilities R.family (v.refine w) S ∧ Foundation F Q ∧ (l : Filter _) ≤ (v.refine w).fuse ∧
      cohort l ∧ MatrixTicket (C:=R.family) S F.sector.derivatives (l : Filter _) ∧
      Nesting.Uniform F Q ∧ LogTrace F Q.port ∧ AllTrees F Q := by
  obtain ⟨w,S,F,Q,_,_,l,_,fac,foundation,_,_,_,lo,selected,matrix,uniform,trace⟩ :=
    WilsonCenteredNestedElection.original R simple funded v
  exact ⟨w,S,F,Q,l,fac,foundation,lo,selected,matrix,uniform,trace,same_reader F Q fac.toServices trace⟩

end YM.Integration.WilsonSharpPhysicalTreeDetectorApplication
