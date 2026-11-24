import YM.Integration.ActualWilsonGraphReclosure
import YM.Integration.SelectedCofactorCancellation

/-! The signed flagged insertion of a single graph coefficient, its original
pinned vacuum minors, and the cost of restoring it on the Wilson carrier. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ActualWilsonForcedGraph

open Filter Lattice Wilson RG Marker Source Labels
open Extra.Histories Relay Bid Trace.Physical Trace.Physical.Germ
open Trace.Physical.GermGraph ProjectorNext.Equivariance RG04B.Mark RG16.Guarding
open FullQLocal NativeCoveredCofactorLocalUpdate SelectedCofactorCancellation
open ActualWilsonGraphReclosure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {d i N p : ℕ}

/-- Every partner in the signed insertion carries its original vacuum minor. -/
theorem marked_pinned {n : Side} {F : Frame G d} (X : Rep G n)
    (q : Coefficient F n) (U : Config G n) (s : Finset ℕ) :
    q.marked X s U = ∑ k ∈ s, q.forced k U * pinnedVacuum X U k s := by
  by_cases ha : X.activities.admissible X.p U s
  · rw [Coefficient.marked, if_pos ha]
    apply Finset.sum_congr rfl
    intro k hk
    rw [pinnedVacuum, if_pos ((admitted_iff U k s).2 ⟨ha,hk⟩)]
  rw [Coefficient.marked, if_neg ha]
  symm
  apply Finset.sum_eq_zero
  intro k _
  rw [pinnedVacuum, if_neg (fun h => ha ((admitted_iff U k s).1 h).1), mul_zero]

theorem gas_pinned (X : Rep G (C.side i p)) (q : store C d p i)
    (U : Config G (C.side i p)) :
    gas X q U = (Real.exp (X.exponent U) : ℂ) *
      ∑' s, ∑ k ∈ s, q.forced k U * pinnedVacuum X U k s := by
  simp only [gas, marked_pinned]

/-- A priced realization of the signed gas on the original carrier has zero
canonical graph coordinate and its raw coefficient is charged to that price. -/
theorem gas_coordinate (H : C.Makes) (hi : i≤N) (hp : C.ref d ≤ i)
    (X : Rep G (C.side i p)) (q w : store C d p i) {b : ℝ}
    (hw : reads d N p i w b) (hvalue : value d N p i w = gas X q) :
    page d p i w = 0 ∧
      (C.labels.level d).coeffSize w.x ≤ invoice (C := C) d i p * b := by
  have first : Ink C N p d i (value d N p i w) (page d p i w) b := ⟨w, hw, rfl, rfl⟩
  have hz : Ink C N p d i (0 : Config G (C.side i p) → ℂ) 0 0 := by
    simpa only [zero_smul, norm_zero, zero_mul] using first.scale 0 H hp hi
  obtain ⟨z,hr,hp0,hv0⟩ := hz
  have hnear : value d N p i w =ᶠ[𝓝 1] value d N p i z := by
    filter_upwards [offFlags X.p.threshold X.p.threshold_pos] with U hU
    rw [hvalue, ← hv0]
    exact gas_unflagged X q U hU
  have h0 := (same_page H hi hp hw hr hnear).trans hp0
  refine ⟨h0, ?_⟩
  have h := measured_diff d N p i H hp hi hw
  rw [h0, zero_sub] at h
  simpa only [Frame.coeffSize, Pi.neg_apply, norm_neg] using h

/-- Restoring the gas on the original representation adds precisely its paid
allowance. The coarse readout stays equal to the selected regular germ. -/
theorem restore (H : C.Makes) (hi : i≤N) (hp : C.ref d ≤ i)
    (X : PhysicalCarrier C N p i) (he : X.rep.eval = (C.path.rep N p i).eval)
    (q w : store C d p i) (hf : q.Format 0 C.params X.rep) {k r b : ℝ}
    (hq : q.remBound 0 X.rep k r) (hw : reads d N p i w b)
    (hvalue : value d N p i w = gas X.rep q) :
    Ink C N p d i (q.density 0 (C.localSection d) X.rep)
      (page d p i (purge q)) (r+b) := by
  have hregular : Ink C N p d i (value d N p i (purge q)) (page d p i (purge q)) r :=
    ⟨purge q, regular_price H hi X q hf hq, rfl, rfl⟩
  have hgas : Nullity C N p d i (gas X.rep q) b :=
    ⟨w, hw, (gas_coordinate H hi hp X.rep q w hw hvalue).1, hvalue.symm⟩
  have hs : q.density 0 (C.localSection d) X.rep = value d N p i (purge q) + gas X.rep q :=
    funext (split H hi X he q)
  rw [hs]
  simpa only [add_zero] using hregular.combine hgas H hp hi


section Selected

open MeasureTheory RG3.Script.Picnic LocalComparison LocalComparison.Global
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained
open MergeProof MergeProof.Accent

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  {J : Request V} {A : NumericSchedule C J} {datum : LocalFormal.Datum C Γ}
  {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
  {O : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input}

/-- For a matched original fine column, the whole signed gas insertion has a
priced realization on the original coarse carrier and exact zero germ. -/
theorem selected_gas (T : Retained.ChosenPrimary O) (H : C.Makes)
    (hi : datum.level<datum.cutoff)
    (hf : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (j : V) (x : TestSpace J.tests) (ho : F.coarseRoots j = 0)
    (hp : C.ref (J.outputWeight j) ≤ datum.level)
    (hl : Integrable (I.input.leaf x).density (prior G (C.side (datum.level+1) datum.period)))
    (v : C.label (J.outputWeight j))
    (hv : (fun U => ((I.input.leaf x).density U).part (Γ.fire j)) =
      calValues (C := C) (J.outputWeight j) datum.cutoff datum.period (datum.level+1) v) :
    let d := J.outputWeight j
    let i := datum.level
    let N := datum.cutoff
    let p := datum.period
    let z := ((C.S.block i).val : ℂ)^d
    let q := T.coefficient j x
    ∃ r : ℝ, reads d N p i (purge q) r ∧
      ∀ a : ℝ, Ink C N p d i (calValues (C := C) d N p i v)
        (measuring C d N p i v) a →
        Nullity C N p d i (z • gas O.carrier.rep q) (a+‖z‖*r) := by
  intro d i N p z q
  obtain ⟨r, hregular, hpage, hout⟩ := selected T H hi hf j x ho
  refine ⟨r, hregular, ?_⟩
  intro a ha
  have hr : Ink C N p d i (value d N p i (purge q)) (page d p i (purge q)) r :=
    ⟨purge q,hregular,rfl,rfl⟩
  have hpush : (fun U => ((O.output.leaf x).density U).part (Γ.fire j)) =
      (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
        (fun U => ((I.input.leaf x).density U).part (Γ.fire j)) := by
    rw [← O.density x]
    exact push_get (C.path.levels.transition_mass i p _) hl (Γ.fire j)
  have hactual : calValues (C := C) d N p i v =
      z • (fun U => ((O.output.leaf x).density U).part (Γ.fire j)) := by
    rw [factory_eq d N p i H hp hi v, ← hv, transition, blast, ← hpush]
  have hs : calValues (C := C) d N p i v + (-z) • value d N p i (purge q) =
      z • gas O.carrier.rep q := by
    rw [hactual]
    ext U
    change z * ((O.output.leaf x).density U).part (Γ.fire j) +
      (-z) * value d N p i (purge q) U = z * gas O.carrier.rep q U
    rw [hout U]
    ring
  have h0 : measuring C d N p i v + (-z) • page d p i (purge q) = 0 := by
    have hy := selected_readout T H hi hf j x ho hp hl v hv
    rw [hy, hpage, neg_smul, add_neg_cancel]
  have whole := ha.combine (hr.scale (-z) H hp hi.le) H hp hi.le
  rw [hs, h0, norm_neg] at whole
  exact whole

/-- The actual purchased graph coefficient gives a finite original price
without any assumption of sharp smallness on the selected forced series. -/
theorem factory_gas (T : Retained.ChosenPrimary O) (H : C.Makes)
    (hi : datum.level<datum.cutoff)
    (hf : I.carrier.rep.eval = (C.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (j : V) (x : TestSpace J.tests) (ho : F.coarseRoots j = 0)
    (hp : C.ref (J.outputWeight j) ≤ datum.level)
    (hl : Integrable (I.input.leaf x).density (prior G (C.side (datum.level+1) datum.period)))
    (v : C.label (J.outputWeight j))
    (hv : (fun U => ((I.input.leaf x).density U).part (Γ.fire j)) =
      calValues (C := C) (J.outputWeight j) datum.cutoff datum.period (datum.level+1) v) :
    let d := J.outputWeight j
    let i := datum.level
    let N := datum.cutoff
    let p := datum.period
    let z := ((C.S.block i).val : ℂ)^d
    let q := T.coefficient j x
    ∃ r : ℝ, reads d N p i (purge q) r ∧
      Nullity C N p d i (z • gas O.carrier.rep q)
        (stock C i * (C.labels.level d).coeffSize ((C.factory d N p).entries i v).x + ‖z‖*r) := by
  intro d i N p z q
  obtain ⟨r,hr,h⟩ := selected_gas T H hi hf j x ho hp hl v hv
  exact ⟨r,hr,h _ ⟨(C.factory d N p).entries i v,entryOk d N p i H hp hi.le v,rfl,rfl⟩⟩

end Selected

end YM.Integration.ActualWilsonForcedGraph
