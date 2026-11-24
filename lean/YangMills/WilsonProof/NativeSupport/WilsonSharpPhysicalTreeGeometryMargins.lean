import YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeDoorways

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader OPE.Arboreal OPE.Arboreal.Mountain
open scoped Classical Topology
open private moved from YM.Integration.WilsonNestedReportedCharacterCurrentBayQ343MSExamTreeDoorways

/-- The original tree lifetimes supply the whole-tuple orbit aperture even if two leaves
are arbitrarily closer to each other than the root radius. -/
theorem leaf_margin {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (trace : LogTrace F Q.port) {I : Type} [Fintype I] (tree : Arboreal I)
    (p : I → C.book.Token) (D : I → ℕ) (m : ℕ) {M η : ℝ} (hM : 0 ≤ M) (hη : 0 < η) :
    ∀ᶠ r : ℝ in 𝓝[>]0, ∀ (X : I → E4) (R : I → ℝ), R tree.root = r → tree.Convoy M η R X →
      orbitMargin Q.port m (crop X tree.leaves) (X tree.root) := by
  choose cut paid using fun w : ↥(bands F.sector.derivatives m) =>
    trace.tickets tree p w.1 D M η hM hη
  filter_upwards [Filter.eventually_all.mpr paid] with r ready
  intro X R root conv w live k e he
  let i : ↥(bands F.sector.derivatives m) := ⟨w,live⟩
  exact (ready i (Ortho.move k ∘ X) R root (moved tree conv k) (cut i) le_rfl).lifetimes.outer e he

end YM.Integration.WilsonSharpPhysicalTreeGeometry
