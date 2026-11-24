import YangMills.WilsonProof.NativeSupport.checks.ComparisonCommonWitness

/-!
# RG16 integration binding

Use this with penalty 1. For worker-facing intermediate statements work in universality over
`C`, `H : C.Makes`, `F` etc., generally stating results before any choice of final extraction
(hence applicable to the `Context` data). No q-comparison assumption in `Context`.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16

open Filter

/-- Use ONE of these. No separate picking of Families (not even for the phase extension or
for the additional full-mesh data). -/
structure Context (G : Gauge) (hG : G.Simple) (penalty : ℝ) where
  C : Family G
  f : Extraction.Order
  T : Table C.book
  F : Spec.Final C f T
  L : EveryPhase.Almanac F
  stamped : C.path.levels.clock.kernel.penalty = penalty
  floral : UVExtension.Oasis.Floral (hG := hG) C
  fullMesh : (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T
  margins : ∀ d k : ℕ, ∀ᶠ p in atTop, ∀ (n : ℕ) (v : Fin n → C.book.Token),
    (∀ i, (v i).1 ≤ d) → ∃ g, UVExtension.Poppy.Margins C n p k v g
  completed : EveryPhase.Completed F L

namespace Context
variable {G : Gauge} {hG : G.Simple} {penalty : ℝ} (c : Context G hG penalty)

lemma makes : c.C.Makes := c.F.room.cutoff
lemma calibration : Spec.Calibrated c.C := c.F.calibration

/-- Keeps the construction trajectory and its extraction. -/
theorem supply (G : Gauge) (hG : G.Simple) (hp : 0 < penalty) : Nonempty (Context G hG penalty) := by
  obtain ⟨C, f, T, F, L, -, -, h₁, h₂, h₃, h₄, h₅⟩ :=
    ComparisonPackage.common_uv_every_phase G hG penalty hp
  exact ⟨⟨C, f, T, F, L, h₁, h₂, h₃, h₄, h₅⟩⟩

end Context
end YM.RGComparison.Core16
