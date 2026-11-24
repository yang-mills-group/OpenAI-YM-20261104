import YM.Integration.ActualQLocalGraphDefect
import YM.Integration.FullQLocalRetainedOutput
import YM.RG04B.Mark.Lanes
import YM.RG16.GaugeCredit.Phase

/-! On a canonically reclosed marked step the regular singleton transfers to
the original Wilson representation at its paid norm. The difference is the
literal gas insertion with the selected forced partners, supported on flags. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonGraphReclosure

open Filter MeasureTheory Lattice Wilson RG Marker Source Labels
open Extra.Histories Relay Bid Trace.Physical Trace.Physical.Germ
open Trace.Physical.GermGraph ProjectorNext.Equivariance
open RG04B.Mark FullQLocal LocalComparison MergeProof MergeProof.Accent RG16.Guarding
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {d i N p : ℕ}

/-- The unnormalized linear insertion into the selected physical gas. -/
def gas (X : Rep G (C.side i p)) (q : store C d p i) (U : Config G (C.side i p)) : ℂ :=
  (Real.exp (X.exponent U) : ℂ) * ∑' b, q.marked X b U

theorem gas_unflagged (X : Rep G (C.side i p)) (q : store C d p i)
    (U : Config G (C.side i p)) (h : flags X.p.threshold U = ∅) : gas X q U = 0 := by
  unfold gas
  simp_rw [unflagged h, tsum_zero, mul_zero]

/-- This equality holds on every field, including the flagged region. -/
theorem split (H : C.Makes) (hi : i≤N) (X : PhysicalCarrier C N p i)
    (he : X.rep.eval = (C.path.rep N p i).eval) (q : store C d p i)
    (U : Config G (C.side i p)) :
    q.density 0 (C.localSection d) X.rep U =
      value d N p i (purge q) U + gas X.rep q U := by
  let Y := C.path.rep N p i
  have hp : X.rep.p = Y.p := X.point.trans (H.wilson.represents N p i hi).vac.symm
  have hz (b : Finset ℕ) : (purge q).marked Y b U = 0 := by
    unfold Coefficient.marked
    split_ifs <;> simp [purge]
  have hr : q.exponentialEntry 0 (C.localSection d) X.rep U =
      (purge q).exponentialEntry 0 (C.localSection d) Y U := by
    simp only [Coefficient.exponentialEntry, Coefficient.maskedTerm, purge, hp]
  change q.density 0 (C.localSection d) X.rep U =
    (purge q).density 0 (C.localSection d) Y U + gas X.rep q U
  simp only [Coefficient.density, hz, tsum_zero, mul_zero, add_zero, gas, he, hr]
  rfl

/-- Dropping the forced partners preserves the original ordinary allowance
even when the selected source was presented with a different forced divisor. -/
theorem regular_price (H : C.Makes) (hi : i≤N) (X : PhysicalCarrier C N p i)
    (q : store C d p i) (hformat : q.Format 0 C.params X.rep) {k r : ℝ}
    (hq : q.remBound 0 X.rep k r) : reads d N p i (purge q) r := by
  have hp := X.point.trans (H.wilson.represents N p i hi).vac.symm
  obtain ⟨a,b,ha,hb,hab,_,he,_⟩ := hq
  refine ⟨⟨?_,hformat.origin,hformat.identity_null,hformat.projects,
    fun _ _ h => False.elim (h rfl), fun _ h => False.elim (h rfl),
    fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ => measurable_const⟩,
    a,0,ha,le_rfl,(add_le_add le_rfl hb).trans hab,
    Real.sqrt_pos.2 (Extra.Histories.forcedPos ..), ?_, ?_⟩
  · exact hp ▸ hformat.smooth
  · exact hp ▸ he
  · rw [mul_zero]
    exact ⟨fun _ => 0, budget0 _ _, fun _ => ⟨le_rfl, fun _ => (norm_zero (E := ℂ)).le⟩⟩

section Selected

open RG3.Script.Picnic LocalComparison.Global FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C Γ}
  {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
  {O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input}

/-- A retained singleton already supplies the priced regular coefficient on
the original Wilson carrier. Its full readout keeps the selected signed gas
insertion at all configurations and exactly the selected intrinsic germ. -/
theorem selected (T : Retained.ChosenPrimary O) (H : C.Makes) (hi : datum.level<datum.cutoff)
    (hf : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (j : V) (x : TestSpace J.tests) (ho : F.coarseRoots j = 0) :
    let q := T.coefficient j x
    ∃ r : ℝ, reads (J.outputWeight j) datum.cutoff datum.period datum.level (purge q) r ∧
      page (J.outputWeight j) datum.period datum.level (purge q) =
        projection (C.labels.level (J.outputWeight j)) C.params O.carrier.rep.p.threshold
          (F.coarseRoots j) q ∧
      ∀ U, ((O.output.leaf x).density U).part (Γ.fire j) =
        value (J.outputWeight j) datum.cutoff datum.period datum.level (purge q) U +
          gas O.carrier.rep q U := by
  let q := T.coefficient j x
  have hp := O.carrier.point
  have hfmt := T.format j x
  obtain ⟨k,r,hr⟩ := T.remainder j x
  rw [ho] at hfmt hr
  have he := O.output_vacuum H hi hf
  refine ⟨r, regular_price H hi.le O.carrier q hfmt hr, ?_, ?_⟩
  · rw [ho, hp]
    rfl
  · intro U
    have hs := (T.singleton j x U).symm
    rw [ho] at hs
    exact hs.trans (split H hi.le O.carrier he q U)

/-- If the selected fine singleton is the specified genuine factory column,
its original coarse matrix readout is the selected intrinsic coefficient,
with precisely the engineering factor from the physical transition. -/
theorem selected_readout (T : Retained.ChosenPrimary O) (H : C.Makes)
    (hi : datum.level<datum.cutoff)
    (hf : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (j : V) (x : TestSpace J.tests) (ho : F.coarseRoots j = 0)
    (hp : C.ref (J.outputWeight j) ≤ datum.level)
    (hl : Integrable (I.input.leaf x).density (prior G (C.side (datum.level+1) datum.period)))
    (v : C.label (J.outputWeight j))
    (hv : (fun U => ((I.input.leaf x).density U).part (Γ.fire j)) =
      calValues (C := C) (J.outputWeight j) datum.cutoff datum.period (datum.level+1) v) :
    measuring C (J.outputWeight j) datum.cutoff datum.period datum.level v =
      ((C.S.block datum.level).val : ℂ)^(J.outputWeight j) •
        projection (C.labels.level (J.outputWeight j)) C.params O.carrier.rep.p.threshold
          (F.coarseRoots j) (T.coefficient j x) := by
  let d := J.outputWeight j
  let i := datum.level
  let p := datum.period
  let N := datum.cutoff
  let z := ((C.S.block i).val : ℂ)^d
  let q := T.coefficient j x
  obtain ⟨r, hread, hpage, hout⟩ := selected T H hi hf j x ho
  have hprimary : Ink C N p d i (value d N p i (purge q)) (page d p i (purge q)) r :=
    ⟨purge q, hread, rfl, rfl⟩
  obtain ⟨W, hW, hWpage, hWvalue⟩ := hprimary.scale z H hp hi.le
  have hpush : (fun U => ((O.output.leaf x).density U).part (Γ.fire j)) =
      (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
        (fun U => ((I.input.leaf x).density U).part (Γ.fire j)) := by
    rw [← O.density x]
    exact push_get (C.path.levels.transition_mass i p _) hl (Γ.fire j)
  have hactual : calValues (C := C) d N p i v =
      z • (fun U => ((O.output.leaf x).density U).part (Γ.fire j)) := by
    rw [factory_eq d N p i H hp hi v, ← hv, transition, blast, ← hpush]
  have hnear : value (C := C) d N p i ((C.factory d N p).entries i v) =ᶠ[𝓝 1]
      value d N p i W := by
    filter_upwards [offFlags O.carrier.rep.p.threshold O.carrier.rep.p.threshold_pos] with U hU
    change calValues (C := C) d N p i v U = value d N p i W U
    rw [hactual, ← hWvalue]
    change z * ((O.output.leaf x).density U).part (Γ.fire j) = z * value d N p i (purge q) U
    rw [hout U, gas_unflagged O.carrier.rep q U hU, add_zero]
  have hid := same_page H hi.le hp (entryOk d N p i H hp hi.le v) hW hnear
  exact hid.trans (hWpage.trans (congrArg (fun w => z • w) hpage))

/-- The selected primary budget is the actual coarse readout error of the
native factory column, with the original test radius and kernel cost. -/
theorem readout_error (T : Retained.ChosenPrimary O) {e : ℝ} (hT : T.Bound e)
    (H : C.Makes) (hi : datum.level<datum.cutoff)
    (hf : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (j : V) (x : IndependentTests J.tests) (ho : F.coarseRoots j = 0)
    (hp : C.ref (J.outputWeight j) ≤ datum.level)
    (hl : Integrable (I.input.leaf (testInclusion J.tests x)).density
      (prior G (C.side (datum.level+1) datum.period)))
    (v : C.label (J.outputWeight j))
    (hv : (fun U => ((I.input.leaf (testInclusion J.tests x)).density U).part (Γ.fire j)) =
      calValues (C := C) (J.outputWeight j) datum.cutoff datum.period (datum.level+1) v) :
    let z := ((C.S.block datum.level).val : ℂ)^(J.outputWeight j)
    (F.outputRadii j / F.kernelCosts j) * (C.labels.level (J.outputWeight j)).coeffSize
      (measuring C (J.outputWeight j) datum.cutoff datum.period datum.level v -
        z • vector (C.labels.level (J.outputWeight j)) C.params O.carrier.rep.p.threshold
          (F.coarseRoots j) (fun U =>
            (O.model.read (testInclusion J.tests x) (Pert.Asymptotics.regulatorRun C
              datum.cutoff datum.period (datum.level+1)) U).part (Γ.fire j))) ≤ ‖z‖*e := by
  intro z
  rw [selected_readout T H hi hf j (testInclusion J.tests x) ho hp hl v hv]
  change (F.outputRadii j / F.kernelCosts j) *
    (C.labels.level (J.outputWeight j)).coeffSize (z • _ - z • _) ≤ ‖z‖*e
  rw [← smul_sub, Size.smul]
  exact (mul_left_comm _ _ _).le.trans (mul_le_mul_of_nonneg_left (hT j x) (norm_nonneg z))

end Selected
end YM.Integration.ActualWilsonGraphReclosure
