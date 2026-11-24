import YM.GapsContact.Focus
import YM.TraceExtension.Endpoint
/-!
# Every-phase spectral and finite-order matching result

All statements about `focus X i` refer to character i of precisely the F below —
`L.contours i`, `L.actors i`, same fields (trace centering takes the i-vacuum subtraction).
The log-rescaled distributional limit includes the timelike and null tests.

In `Flight` all these character-phase results are ALSO in the same aligned X-frame
and coupling of the finite-order prescription of 9637, and `κ, d, e` are literally the
same real functions. In particular the predictions in `FieldComparison` involving the
*selected* phase (e.g. in its E diagnostic convergence and centered field identity) now apply,
on those common choices, in every character phase. No assertion of uniformity over phase yet.
Do not infer this from, e.g., full-support a.e. and continuity; we use additional universality
of the Trace producer for the focus Finals.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact
open Function Set Filter Spec Boundary TraceExtension Trace Trace.Target Trace.Pilot
open Trace.Over Trace.Terrace Trace.Pith Spin EveryPhase Extraction Table
open scoped Topology
universe u
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Final C f S} {L : Almanac F} (X : Completed F L) (i : F.α.space.X)

lemma center_focus : center (focus X i) = center F +
    (euclideanVEV S (selected F) (stressTrace F.sector.energy) -
      euclideanVEV S (F.α.ensemble i) (stressTrace F.sector.energy)) • S.unit 4 := by
  let a := stressTrace F.sector.energy
  let s := S.unit 4
  let p := euclideanVEV S (selected F) a
  let q := euclideanVEV S (F.α.ensemble i) a
  change a - q • s = a - p • s + (p - q) • s
  rw [sub_smul]
  abel

lemma tendC_focus {P : ℝ → change S 4} {d : ℝ → ℝ} (ht : TendC F P d) :
    TendC (focus X i) P d := by
  refine ⟨ht.measures, ?_, ht.tensor⟩
  let a := stressTrace F.sector.energy
  let q := euclideanVEV S (selected F) a - euclideanVEV S (F.α.ensemble i) a
  obtain ⟨c, hc⟩ := ht.centered
  refine ⟨c + q, hc.mono fun r hr => ?_⟩
  rw [center_focus, smul_add, hr, add_smul, smul_add, add_assoc]

/-- Move every receipt to the *same* post-position frame and the *same* computed
coefficients, no UV/period limits taken over phases. -/
lemma fieldComparison_focus {h : G.Simple} {H : (Climb.Bel C.book).Hierarchy} {Z : Arch C}
    {P P' : ℝ → change S 4} {κ d e : ℝ → ℝ}
    (R : Result.{u} (focus X i) h)
    (Y : FieldComparison F H Z P P' κ d e) : FieldComparison (focus X i) H Z P P' κ d e :=
  fieldComparison_of (focus X i) h ⟨Y.alignment.spun, Y.alignment.near⟩
    Y.positions Y.calibrationX Y.wilson Y.coupling (tendC_focus X i Y.leading)
    Y.spinTwo (Y.measures.mono fun _ h => ⟨h.reads⟩) Y.coefficient_O R.shortDistance

structure Flight (F : Final C f S) (h : G.Simple) (L : Almanac F) : Prop where
  complete : Completed F L
  trace : Result.{u} F h
  every (i : F.α.space.X) : Result.{u} (focus complete i) h
  commonFrame : ∃ (H : (Climb.Bel C.book).Hierarchy), ∃ Z l χ P P' κ d e,
    Bliss F l Z H ∧ XScheme F h H l P P' χ ∧
    FieldComparison F H Z P P' κ d e ∧
    ∀ i : F.α.space.X, FieldComparison (focus complete i) H Z P P' κ d e

include X in
lemma Flight.join {h : G.Simple} (A : ∀ F : Final C f S, Result.{u} F h) : Flight.{u} F h L := by
  refine ⟨X, A F, fun i => A (focus X i), ?_⟩
  obtain ⟨H,Z,l,hl,⟨χ,P,P',hχ⟩,hx⟩ := (A F).stress
  obtain ⟨κ,d,e,Y⟩ := hx χ P P' hχ
  exact ⟨H,Z,l,χ,P,P',κ,d,e,hl,hχ,Y, fun i => fieldComparison_focus X i (A (focus X i)) Y⟩

/-- Workhorse existential. Higher *perturbative* orders & horizons of matching are NOT
asserted here. Distinct from any C with stronger UV convergence than `main`; extraction
uses its same filters. -/
theorem everyTrace (G : Gauge) (h : G.Simple) (b : ℝ) (hb : 0 < b) (p : Extraction.Order) :
    ∃ C : Family G, C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=b ∧
      Extraction.Wcmain C ∧ ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Spec.Final C (p.refine q) S) (L : Almanac F), Flight.{u} F h L := by
  obtain ⟨C,hC,hK,hB,hW,q,⟨S,⟨F⟩⟩,hF⟩ := Trace.Target.main.{u} G h b hb p
  obtain ⟨L,hL⟩ := all_characters F
  exact ⟨C,hC,hK,hB,hW,q,S,F,L,Flight.join hL (hF S)⟩

end YM.GapsContact
