import YM.Integration.WilsonGraphMixedOriginalNumeratorNames
import YM.Integration.WilsonGraphOriginalCompactWords

/-! The original all-r near and far numerator on the separated compact of the correlation publication. -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.GradedFar.AppointedMixedCompact

open Function Filter Real Set Growth Continuation
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Book MS.Land Scale Register O O.Enh O.Score Dframe
open YangMills YangMills.Matching YM.Answer.ContinuumLimit YM.Integration YM.OPE YM.OPE.Orbits
open AppointedMixedFarRow WilsonGraphPublishedShapeEstimate
open scoped Topology BigOperators Classical

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev selected := WilsonGraphPaperPublication.publicPick.{u} g hg (ElectedPublication.order periods strict)
private abbrev scheme := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev model := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev table := YangMills.hierarchy (g := g) (selected.{u} g hg periods strict).pupil.last (selected.{u} g hg periods strict).pupil.P
private abbrev conversion := _root_.IssuedBridge.PostedAppointedConversion.filed (scheme g hg) (model.{u} g hg).MS
  (model.{u} g hg).matching (Teller.logNu 1)
private abbrev heat := ElectedMeasurement.clock (selected.{u} g hg periods strict) (scheme g hg)

variable {n m : ℕ}

theorem onCompact (cap q : ℕ) {K : Set (YM.Points (n+m))} (compact : IsCompact K)
    (safe : K ⊆ YM.conf (n+m)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ (s : ℝ) (w : Fin (n+m) → ℕ), (∀ i, w i ≤ cap) →
      ∀ (a : (i : Fin (n+m)) → Sec g.core (w i)) (phase : Option (table.{u} g hg periods strict).Character)
        (o : Spacetime) (z : YM.Points n × YM.Points m), placement s z ∈ K →
        ‖observed.{u} g hg periods strict w a r s phase o z -
          crop q (heat.{u} g hg periods strict r) (series g hg w a s z)‖ ≤
          A*(∏ i, sectorMass (B := _root_.IssuedMaxwell.Reports.B g) (a i))*|heat.{u} g hg periods strict r|^(q+1) := by
  have receipt := AppointedCompactWords.value.{u} g hg periods strict cap q K compact safe
  let A := receipt.choose
  have event := receipt.choose_spec.2
  refine ⟨A,receipt.choose_spec.1,?_⟩
  filter_upwards [event,(show ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r from self_mem_nhdsWithin)] with r paid hr
  intro s w within a phase o z hz
  let θ := heat.{u} g hg periods strict r
  let X := AppointedCompactWords.original.{u} g hg periods strict r w a phase o
  let F := AppointedCompactWords.polynomial.{u} g hg w a q θ
  have physical : observed.{u} g hg periods strict w a r s phase o z = X (placement s z) :=
    (names.{u} g hg periods strict w a hr s phase o z (safe hz)).symm
  have formal : crop q θ (series g hg w a s z) = F (placement s z) := by
    rw [YM.FVA2.GradedFar.crop_eq]
    exact (AppointedMixedBook.filedAtPorts.{u} g hg w a z.1 z.2 q s θ (safe hz)).trans
      (referenceSum (conversion.{u} g hg) (publicLetters w a) (placement s z) q θ)
  have e₁ := congrArg (fun v : ℂ => ‖v-crop q θ (series g hg w a s z)‖) physical
  have e₂ := congrArg (fun v : ℂ => ‖X (placement s z)-v‖) formal
  exact (e₁.trans e₂).le.trans (paid w within a phase o (placement s z) hz)

end YM.FVA2.GradedFar.AppointedMixedCompact
end

