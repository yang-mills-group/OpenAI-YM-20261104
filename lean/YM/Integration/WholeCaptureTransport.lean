import YM.Integration.CalibratedCellMatch
import YM.RG16.GaugeCredit.Phase

/-! The signed single and forced components of a funded replica match determine
one density on the Wilson family. Its actual post-step propagators carry that
density and the calibrated counterterm through the interval. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WholeCaptureTransport
open Lattice Wilson RG Source Filter Function MeasureTheory Labels Extraction Next
open Push Local Bid Cells Extra.Histories Relay Motion Overlay MergeProof MergeProof.Accent
open RG16.Literal RG16.Guarding Trace.Physical.GermGraph PhysicalNext.Repeat
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} (C : Family G) (N p d : ℕ)
set_option quotPrecheck false

/-- On a lawful vacuum, the complete signed exponential and forced-profile
identities determine the value, including the dressed forced activities. -/
theorem density_ext {i : ℕ} (H : C.Makes) (hi : i ≤ N)
    {P Q : store C d p i} {r s : ℝ}
    (hp : reads d N p i P r) (hq : reads d N p i Q s)
    (he : P.exponentialEntry 0 (C.localSection d) (C.path.rep N p i) =
      Q.exponentialEntry 0 (C.localSection d) (C.path.rep N p i))
    (hf : profile (C.path.rep N p i).activities P.forced =
      profile (C.path.rep N p i).activities Q.forced) :
    value (C := C) d N p i P = value d N p i Q := by
  let good := (H.wilson.represents N p i hi).good
  have hP := rem_dominated hp.2
  have hQ := rem_dominated hq.2
  funext U
  unfold value Coefficient.density
  rw [he, dress_eq good hP, dress_eq good hQ]
  rw [chamber (funext fun j => congrFun (congrFun hf j) U) U
    ((dress_abs good hP).summable _) ((dress_abs good hQ).summable _)]

/-- The exact raw page of the total source, with its calibrated term still
in the native terminal coordinates. The signed residual pays its foreground
bill directly in the same Wilson representation. -/
theorem read_signed {i : ℕ} (H : C.Makes) (ho : Opened C d i p)
    (hi : i ≤ N) {f : Cut C N p} (b : C.label d) {P : store C d p i}
    {r : ℝ} (hp : reads d N p i P r)
    (hval : credit C N p d f i hi =
      value (C := C) d N p i P + calValues d N p i b) :
    Booked C N p d f i hi ∧
    measuring C d N p i (topReport C N p d H i ho hi f - b) = page d p i P ∧
    Foreground C d N p i (credit C N p d f i hi - calValues d N p i b)
      ((1 + 4 * stock C i) * (r + (C.labels.level d).coeffSize P.x)) := by
  let A := (C.factory d N p).entries i b
  have hA := entryOk d N p i H ho.post hi b
  have hh := presentation hp.1 hp.2 hA.1 hA.2
  have hv : credit C N p d f i hi = value (C := C) d N p i (beside P A) :=
    hval.trans (plus (H.wilson.represents N p i hi).good hp.2 hA.2 (C.localSection d)).symm
  have hpage := readPage_eq C N p d f H hi ho.post (beside P A) hh hv
  have hr : 0 ≤ r := rem_nonneg hp.2
  have hx := Work.G08.size_nonneg (C.labels.level d) P.x
  refine ⟨⟨beside P A, _, hh, hv⟩, ?_, ?_⟩
  · change (fitting d N p i H ho hi) (_ - b) = _
    rw [map_sub, topReport, LinearEquiv.apply_symm_apply, hpage,
      addPage d N p i P A H ho.post hi hp hA]
    exact add_sub_cancel_right _ _
  · rw [hval, add_sub_cancel_right]
    exact foreground_fee (a := r + (C.labels.level d).coeffSize P.x)
      ⟨hp.1, rem_increase d hp.2 (le_add_of_nonneg_right hx)⟩
      (le_add_of_nonneg_left hr) le_rfl

variable {W : Worth} {u ψ φ δ : ℕ → ℝ} {r : ℕ → ℕ} {ζ : ℕ → ℕ → ℝ}
variable {D : ∀ N p i : ℕ, i < N → GaugeDoor (C.path.rep N p (i+1)) (C.path.rep N p i)}
variable (m b J : ℕ) (h : Scrim C W u ψ φ δ ζ r D) (w : ℝ)
local notation "R" => C.path.rep N p
local notation "σ" => (C.labels.level d).coeffSize

/-- A prescribed calibrated cell and the whole funded replica give one
identical signed trajectory on every original propagator, complete bookings,
and the exact intrinsic end-coordinate correction. -/
theorem matched_path (H : C.Makes) (ho : Opened C d m p) (hJ : J ≤ m)
    (hm : m ≤ b) (hb : b ≤ N) {E t : ℝ}
    (f : Cut C N p) (hf : Continuous f) (Q : store C d p b) (B : C.label d)
    (hQ : reads d N p b Q t)
    (hmatch : CalibratedCellMatch.Matched C N b m p d w h Q ho.post hm hb E B)
    (hF : Fleet C N p d b J f (hJ.trans (hm.trans hb))
      (march (fun _ : Site (C.side J p) => w) φ m b) Q hb) :
    ∃ (P : ∀ i, store C d p i) (g : ℕ → ℝ),
      Club C.path C.params (C.localSection d) (ζ d) ψ m b N p
        (stair φ (2*w) m) D P g hb ∧
      ∀ i, m ≤ i → ∀ hi : i ≤ b,
        (let y := (C.factory d N p).terminal.symm B
         credit C N p d f i (hi.trans hb) = value d N p i (P i) + calValues d N p i y) ∧
        Booked C N p d f i (hi.trans hb) ∧
        (∀ hiO : Opened C d i p, measuring C d N p i
          (topReport C N p d H i hiO (hi.trans hb) f - (C.factory d N p).terminal.symm B) =
          page d p i (P i)) ∧
        Foreground C d N p i (credit C N p d f i (hi.trans hb) -
          calValues d N p i ((C.factory d N p).terminal.symm B))
          ((1+4*stock C i)*(g i+σ (P i).x)) := by
  let X := (h.costs.aim d N p (ho.post.trans (hm.trans hb))).lyrics.choose
  let z := (C.factory d N p).terminal.symm B
  obtain ⟨hX, hL, _, _⟩ := (h.costs.aim d N p (ho.post.trans (hm.trans hb))).lyrics.choose_spec
  obtain ⟨P, g, hclub, _, hsingle, hforced⟩ := hmatch
  let A := (C.factory d N p).entries b (-z)
  have hA := entryOk d N p b H (ho.post.trans hm) hb (-z)
  have hplays : (C.factory d N p).entries b (-z) = (X.tone b).plays (-z) := by
    rw [show (C.factory d N p).entries = (X.draft C.path).inits from hX]
    rfl
  have hP := hclub.ticks b hm le_rfl
  have he : (P b).exponentialEntry 0 (C.localSection d) (R b) =
      (beside Q A).exponentialEntry 0 (C.localSection d) (R b) := by
    rw [duo_exp (C.localSection d) hQ.2 hA.2, hplays]
    exact hsingle
  have hs : profile (R b).activities (P b).forced = profile (R b).activities (beside Q A).forced := by
    rw [duo_profile hQ.2 hA.2, hplays]
    exact hforced
  have hd := density_ext C N p d H hb hP (presentation hQ.1 hQ.2 hA.1 hA.2) he hs
  have hV := Fleet.keeps C N p d b J H f hf (hJ.trans hm) hb _ Q hQ hF
  have hr : value (C := C) d N p b (P b) =
      credit C N p d f b hb + calValues d N p b (-z) :=
    hd.trans ((plus (H.wilson.represents N p b hb).good hQ.2 hA.2 (C.localSection d)).trans
      (congrArg (· + calValues (C := C) d N p b (-z)) hV.symm))
  refine ⟨P,g,hclub,?_⟩
  intro i hmi hi
  have hE := match_step C N p d b m P H ho hb hclub f hf B hr i hmi hi
  have hp := hclub.ticks i hmi hi
  let A' := (C.factory d N p).entries i z
  have hA' := entryOk d N p i H (ho.post.trans hmi) (hi.trans hb) z
  have hval : credit C N p d f i (hi.trans hb) = value (C := C) d N p i (beside (P i) A') :=
    hE.trans (plus (H.wilson.represents _ _ _ (hi.trans hb)).good hp.2 hA'.2 (C.localSection d)).symm
  have ht : 0 ≤ g i := rem_nonneg hp.2
  have hx := Work.G08.size_nonneg (C.labels.level d) (P i).x
  refine ⟨hE, ⟨_,_,presentation hp.1 hp.2 hA'.1 hA'.2,hval⟩,
    fun hiO => (read_signed C N p d H hiO (hi.trans hb) z hp hE).2.1, ?_⟩
  rw [hE, add_sub_cancel_right]
  exact foreground_fee (a := g i + σ (P i).x)
    ⟨hp.1, rem_increase d hp.2 (le_add_of_nonneg_right hx)⟩ (le_add_of_nonneg_left ht) le_rfl

end YM.Integration.WholeCaptureTransport
