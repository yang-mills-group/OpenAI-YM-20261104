import YangMills.WilsonProof.NativeSupport.MatchingNesting
import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometrySpectators
import YM.Integration.WilsonSharpPhysicalTreeDetectorSelectedPupilClient

/-! The spectator field of the public separated finite-tree statement on the literal
hierarchy returned by the published refinement. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonSharpPhysicalTreeDetectorPublishedDaughter
open Filter Set YangMills YangMills.Hierarchy WilsonGraphPaperPublication
open scoped Classical Topology

/-- The full through-h remainder in the public `SeparatedNestedPowerLog` signature,
with precisely the same exterior and every phase of the issued daughter. -/
theorem original (g : GaugeGroup) (hg : g.IsSimple) (p : ℕ → ℕ) (hp : StrictMono p) :
    let T := (((issued.{u}).runs g hg).refine p hp).hierarchy
    ∀ (t : FusionTree) (a : Fin t.leaves → T.Tag) {J : Type} [Fintype J]
      (b : J → T.Tag) (h : ℕ) (o : Spacetime) (M η c : ℝ), 0 ≤ M → 0 < η → 0 < c →
      ∀ (K : Set (J → Spacetime)), IsCompact K → (∀ y ∈ K, Clear o y c) →
      ∃ β ∈ Set.Ioo (0 : ℝ) 1, ∃ A : ℝ, 0 < A ∧ ∃ k : ℕ, ∀ᶠ r : ℝ in 𝓝[>]0,
        ∀ s x z, t.Admissible r β M η s x z → z 0 = o → ∀ y ∈ K, ∀ phase,
          ‖T.grouped phase a x b y - T.truncatedWithSpectators h phase a x o b y‖ ≤
            A * t.bound T ((h : ℝ) + 1) a s k := by
  let ξ := YM.Answer.ContinuumLimit.ElectedPublication.order p hp
  let V := publicPick.{u} g hg ξ
  obtain ⟨hierarchy,_,_,tested⟩ := WilsonSharpPhysicalTreeDetectorSelectedPupilClient.original.{u} g hg p hp
  rw [hierarchy]
  intro _ t a J _ b h o M η c hM hη hc K _ clear
  exact WilsonSharpPhysicalTreeGeometry.spectator_remainder_from V.pupil.last V.pupil.P tested
    t a b h o M η c hM hη hc K clear

end YM.Integration.WilsonSharpPhysicalTreeDetectorPublishedDaughter
