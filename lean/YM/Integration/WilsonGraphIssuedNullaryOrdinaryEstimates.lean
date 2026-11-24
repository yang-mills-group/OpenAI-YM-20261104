import YangMills.WilsonProof.NativeSupport.Commissioned122.AppointedPublicGraphVacuum
import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets

/-! The empty-input ordinary comparison in the public shape estimate on the issued hierarchy. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedEmptyEstimates

open Function Set Filter MeasureTheory
open XSpace XSpace.Normalize Register Scale Dframe Trace.Pilot Integration
open O O.Score OPE OPE.Orbits Compare
open YangMills YangMills.MSbar
open YM.Answer.ContinuumLimit YangMills.Matching IssuedMaxwell IssuedMaxwell.Reports
open scoped BigOperators Classical Topology ContDiff

universe u
variable (g : YangMills.GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev V := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev H := AppointedOrdinaryPacket.measurement hg (V.{u} g hg periods strict)
  (N g hg) (WilsonGraphPaperPublication.perspective.{u} g hg)

/-- The one physical radius tail precedes all formal crops, output duals, derivatives and tests. -/
theorem everyCrop (h : ℕ) (d : Fin 0 → ℕ) :
    ∀ᶠ r in trail, ∀ (o : E4) (v : Appointed122Fields g.core d) (a : Fin 0 → Ordinary.Label (B g))
      (out : Sec g.core h →ₗ[ℂ] ℂ) (p j : ℕ),
      let physical := fun x : Points 0 =>
        out ((H.{u} g hg periods strict).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x)
      let formal := fun x : Points 0 =>
        out (AppointedPublicGraphVacuum.graphCrop g hg a h p ((V.{u} g hg periods strict).T (N g hg) r) x)
      (∀ x, shapeJetEstimateAt j physical formal x 0) ∧
      ∀ (l : ℕ) (ds : Fin l → Points 0) (μ : Measure (Points 0)) (φ : Points 0 → ℂ),
        (∫ x, φ x * iteratedFDeriv ℝ l (fun y => physical y - formal y) x ds ∂μ) = 0 := by
  filter_upwards [AppointedPublicNullary.measured.{u} g hg periods strict d h] with r paid
  intro o v a out p j
  let physical := fun x : Points 0 =>
    out ((H.{u} g hg periods strict).wilsonOPE r h (fun i : Fin 0 => ⟨d i,v i⟩) o x)
  let formal := fun x : Points 0 =>
    out (AppointedPublicGraphVacuum.graphCrop g hg a h p ((V.{u} g hg periods strict).T (N g hg) r) x)
  have physicalLeaf : physical = fun _ => out (leaf g.core h) :=
    funext fun x => congrArg out (paid x o v)
  have formalLeaf : formal = fun _ => out (leaf g.core h) := funext fun x => congrArg out
    (AppointedPublicGraphVacuum.filedValue.{u} g hg d v a h p ((V.{u} g hg periods strict).T (N g hg) r) x).2
  have diff : (fun x => physical x - formal x) = (0 : Points 0 → ℂ) := by
    funext x
    rw [physicalLeaf,formalLeaf]
    exact sub_self _
  change (∀ x, shapeJetEstimateAt j physical formal x 0) ∧ _
  refine ⟨?_,?_⟩
  · intro x
    refine ⟨?_,?_,?_⟩
    · rw [physicalLeaf]
      exact contDiffAt_const
    · rw [formalLeaf]
      exact contDiffAt_const
    · intro l hl
      rw [diff]
      simp
  · intro l ds μ φ
    change (∫ x, φ x * iteratedFDeriv ℝ l (fun y => physical y - formal y) x ds ∂μ) = 0
    rw [diff]
    simp

end YM.FVA2.GradedFar.AppointedEmptyEstimates
end

