import YM.Integration.WilsonGraphIssuedNullaryOrdinaryEstimates

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar.AppointedEmptyPublicShape
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
private abbrev H := AppointedOrdinaryPacket.measurement hg (V.{u} g hg periods strict) (N g hg)
  (WilsonGraphPaperPublication.perspective.{u} g hg)
private abbrev S := (WilsonGraphGroupPositionReference.external g hg).conversion.conversion

/-- The true empty packet prices the full public finite crop and every shape derivative with zero cost. -/
theorem empty (h q j : ℕ) (d : Fin 0 → ℕ) (K : Set (YM.Points 0)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin 0) → (YangMills.maxwellReference g).sector (d i))
        (o : YangMills.Spacetime) (x : YM.Points 0), x ∈ K →
      ∀ out : (YangMills.maxwellReference g).sector h →ₗ[ℂ] ℂ,
        (∀ w, ‖out w‖ ≤ YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) w) →
      let a : Fin 0 → YangMills.Matching.Label (YangMills.maxwellReference g) := fun i => ⟨d i,v i⟩
      let t := (H.{u} g hg periods strict).clock r
      YangMills.Matching.shapeJetEstimateAt j
        (fun y => out ((H.{u} g hg periods strict).wilsonOPE r h a o y))
        (fun y => out (∑ k : Fin (q+1), (t : ℂ)^k.val • (S g hg).ope
          (_root_.IssuedMaxwell.GraphCoefficients.issued g) h k.val a y))
        x (A * (∏ i, YangMills.Matching.sectorMass (B := YangMills.maxwellReference g) (v i)) * |t|^(q+1)) := by
  refine ⟨0,le_rfl,?_⟩
  filter_upwards [AppointedEmptyEstimates.everyCrop.{u} g hg periods strict h d] with r paid
  intro v o x _ out _
  let a : Fin 0 → Ordinary.Label (B g) := fun i => ⟨d i,v i⟩
  let t := (V.{u} g hg periods strict).T (N g hg) r
  have finite :
      (fun y : YM.Points 0 => out (∑ k : Fin (q+1), (t : ℂ)^k.val •
        (S g hg).ope (GraphCoefficients.issued g) h k.val a y)) =
      (fun y => out (AppointedPublicGraphVacuum.graphCrop g hg a h q t y)) := by
    funext y
    apply congrArg out
    exact Fin.sum_univ_eq_sum_range
      (fun k => (t : ℂ)^k • (S g hg).ope (GraphCoefficients.issued g) h k a y) (q+1)
  simp only [zero_mul]
  change shapeJetEstimateAt j (fun y => out ((H.{u} g hg periods strict).wilsonOPE r h a o y))
    (fun y => out (∑ k : Fin (q+1), (t : ℂ)^k.val • (S g hg).ope
      (GraphCoefficients.issued g) h k.val a y)) x 0
  rw [finite]
  exact (paid o v a out q j).1 x

end YM.FVA2.GradedFar.AppointedEmptyPublicShape
end

