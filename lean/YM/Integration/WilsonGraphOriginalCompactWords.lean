import YM.Integration.WilsonGraphCenteredFarReplacement

/-! The two R4868 estimates on the explicit public coordinates of each original mixed word. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.AppointedCompactWords

open Filter Set YangMills YangMills.Matching YM.Answer.ContinuumLimit
open WilsonGraphPublishedShapeEstimate
open scoped Topology BigOperators Classical ContDiff

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev T := YangMills.hierarchy (g := g) (V.{u} g hg periods strict).pupil.last (V.{u} g hg periods strict).pupil.P
private abbrev B := _root_.IssuedMaxwell.Reports.B g
private abbrev S := _root_.IssuedBridge.PostedAppointedConversion.filed (N g hg) (Q.{u} g hg).MS
  (Q.{u} g hg).matching (FVA2.Teller.logNu 1)
private abbrev t := ElectedMeasurement.clock (V.{u} g hg periods strict) (N g hg)

variable {n : ℕ}

def original (r : ℝ) (w : Fin n → ℕ) (a : (i : Fin n) → (B g).sector (w i))
    (phase : Option (T.{u} g hg periods strict).Character) (o : Spacetime) (x : YangMills.Points n) : ℂ :=
  (T.{u} g hg periods strict).correlation phase
    (fun i => ⟨w i,ElectedMeasurement.frame (V.{u} g hg periods strict) (N g hg) r (w i) (a i)⟩)
    (WithLp.toLp 2 fun i => o+r • x i)

def polynomial (w : Fin n → ℕ) (a : (i : Fin n) → (B g).sector (w i))
    (q : ℕ) (θ : ℝ) (x : YangMills.Points n) : ℂ :=
  ∑ k : Fin (q+1), (θ : ℂ)^k.val * WilsonGraphStandaloneCorrelation.converted
    (S.{u} g hg) k.val (fun i => ⟨w i,a i⟩) x

theorem value (cap q : ℕ) (K : Set (YangMills.Points n)) (compact : IsCompact K) (safe : K ⊆ YM.conf n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (w : Fin n → ℕ), (∀ i, w i ≤ cap) →
      ∀ (a : (i : Fin n) → (B g).sector (w i)) (phase : Option (T.{u} g hg periods strict).Character)
        (o : Spacetime) (x : YangMills.Points n), x ∈ K →
        ‖original.{u} g hg periods strict r w a phase o x -
          polynomial.{u} g hg w a q (t.{u} g hg periods strict r) x‖ ≤
          A*(∏ i, sectorMass (B := B g) (a i))*|t.{u} g hg periods strict r|^(q+1) := by
  exact WilsonGraphCenteredFarReplacement.compactOnPick.{u} g hg periods strict n cap q K compact safe

theorem shape (cap q j : ℕ) (K : Set (YangMills.Points n)) (compact : IsCompact K) (safe : K ⊆ YM.conf n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (w : Fin n → ℕ), (∀ i, w i ≤ cap) →
      ∀ (a : (i : Fin n) → (B g).sector (w i)) (phase : Option (T.{u} g hg periods strict).Character)
        (o : Spacetime) (x : YangMills.Points n), x ∈ K →
        shapeJetEstimateAt j (original.{u} g hg periods strict r w a phase o)
          (polynomial.{u} g hg w a q (t.{u} g hg periods strict r)) x
          (A*(∏ i, sectorMass (B := B g) (a i))*|t.{u} g hg periods strict r|^(q+1)) := by
  have paid : ReferenceShape (N g hg) (V.{u} g hg periods strict) (Q.{u} g hg) :=
    (((WilsonGraphPaperPublication.rowBefore.{u} g hg).choose_spec.2.2
      (fun _ => True) (fun _ _ _ => True.intro)).choose_spec.2.2.2.2.1 (ElectedPublication.order periods strict)).2.1
  exact paid n cap K compact safe q j

end YM.Integration.AppointedCompactWords
end

