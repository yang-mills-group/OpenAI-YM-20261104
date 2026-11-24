import YM.Integration.WilsonGraphPaperCorrelations

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGraphCenteredFarReplacement

open Filter YangMills YangMills.Matching
open YM.Answer.ContinuumLimit WilsonGraphPublishedShapeEstimate WilsonGraphPreElectedShapeEstimates
open scoped Topology BigOperators

universe u
variable (g : GaugeGroup) (hg : g.IsSimple) (periods : ℕ → ℕ) (strict : StrictMono periods)
private abbrev prescription := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev perspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev pick := WilsonGraphPaperPublication.publicPick.{u} g hg
  (ElectedPublication.order periods strict)
private abbrev hierarchy := YangMills.hierarchy (g := g) (pick.{u} g hg periods strict).pupil.last
  (pick.{u} g hg periods strict).pupil.P
private abbrev conversion := _root_.IssuedBridge.PostedAppointedConversion.filed
  (prescription g hg) (perspective.{u} g hg).MS (perspective.{u} g hg).matching (YM.FVA2.Teller.logNu 1)

theorem compactOnPick : CompactReference (prescription g hg) (pick.{u} g hg periods strict) (perspective.{u} g hg) := by
  exact (((WilsonGraphPaperPublication.rowBefore.{u} g hg).choose_spec.2.2
    (fun _ => True) (fun _ _ _ => True.intro)).choose_spec.2.2.2.2.1
      (ElectedPublication.order periods strict)).2.2.1

/-- Express the same physical field in its far-radius chart. -/
def atFar (h : ℕ) (r f : ℝ) (a : (_root_.IssuedMaxwell.Reports.B g).sector h) : (_root_.IssuedMaxwell.Reports.B g).sector h :=
  (ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg) f h).symm (ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg) r h a)

private theorem sameTags (h : ℕ) (r s f : ℝ) (a b : (_root_.IssuedMaxwell.Reports.B g).sector h) :
    ElectedMeasurement.inputs (pick.{u} g hg periods strict) (prescription g hg) f (fun _ : Fin 2 => h)
      ![atFar.{u} g hg periods strict h r f a, atFar.{u} g hg periods strict h s f b] =
      ![⟨h, ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg) r h a⟩, ⟨h, ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg) s h b⟩] := by
  funext i
  fin_cases i <;> simp [ElectedMeasurement.inputs, atFar]

/-- Each physical tag keeps its birth radius. The polynomial uses the complete
pair of submitted coordinates at the common far radius. -/
def PairPrice (h q : ℕ) (A r s f : ℝ) (a b : (_root_.IssuedMaxwell.Reports.B g).sector h)
    (coordinates : Fin 2 → (_root_.IssuedMaxwell.Reports.B g).sector h) (phase : Option (hierarchy.{u} g hg periods strict).Character)
    (o : Spacetime) (x : YangMills.Points 2) : Prop :=
  ‖(hierarchy.{u} g hg periods strict).correlation phase
      ![⟨h, ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg) r h a⟩, ⟨h, ElectedMeasurement.frame (pick.{u} g hg periods strict) (prescription g hg) s h b⟩]
      (WithLp.toLp 2 fun i => o + f • x.ofLp i) -
    ∑ k : Fin (q+1), (ElectedMeasurement.clock (pick.{u} g hg periods strict) (prescription g hg) f : ℂ)^k.val *
      WilsonGraphStandaloneCorrelation.converted (conversion.{u} g hg) k.val (publicLetters (fun _ : Fin 2 => h) coordinates) x‖ ≤
    A * (∏ i, sectorMass (B := (_root_.IssuedMaxwell.Reports.B g)) (coordinates i)) * |ElectedMeasurement.clock (pick.{u} g hg periods strict) (prescription g hg) f|^(q+1)

/-- The two centered pairs share one event at f. -/
theorem centered (h q : ℕ) (K : Set (YangMills.Points 2)) (compact : IsCompact K)
    (separated : K ⊆ YM.conf 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ f : ℝ in 𝓝[>] 0, ∀ (r : ℝ) (a b : (_root_.IssuedMaxwell.Reports.B g).sector h)
      (phase : Option (hierarchy.{u} g hg periods strict).Character) (o y : Spacetime),
      let x : YangMills.Points 2 := WithLp.toLp 2 ![0,y]
      x ∈ K →
        PairPrice.{u} g hg periods strict h q A r r f a b
          ![atFar.{u} g hg periods strict h r f a, atFar.{u} g hg periods strict h r f b] phase o x ∧
        PairPrice.{u} g hg periods strict h q A r f f a b
          ![atFar.{u} g hg periods strict h r f a, b] phase o x := by
  obtain ⟨A,hA,late⟩ := compactOnPick.{u} g hg periods strict 2 h q K compact separated
  refine ⟨A,hA,?_⟩
  filter_upwards [late] with f hf
  intro r a b phase o y x hx
  have pay (s : ℝ) :
      PairPrice.{u} g hg periods strict h q A r s f a b
        ![atFar.{u} g hg periods strict h r f a, atFar.{u} g hg periods strict h s f b] phase o x := by
    have priced := hf (fun _ : Fin 2 => h) (fun _ => le_rfl)
      ![atFar.{u} g hg periods strict h r f a, atFar.{u} g hg periods strict h s f b] phase o x hx
    unfold PairPrice
    rw [← sameTags.{u} g hg periods strict h r s f a b]
    exact priced
  exact ⟨pay r, by simpa only [atFar, LinearEquiv.symm_apply_apply] using pay f⟩

end YM.Integration.WilsonGraphCenteredFarReplacement
end

