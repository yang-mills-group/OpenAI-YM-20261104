import YM.RG3.Forms.Caption
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.MergeProof.Wicket
/-!
# Physical convention for Eq receipts after a represented step

Use literal existing insertions on the SAME C and its bands/rep beta, no
source-dependent offset measure. Conditional denominator is the full scalar
slice integral (= represented eval at j-1 of H *pointwise*) not the kernel
alone. Every slice used here integrable from actual same-budget registration,
void outside orbit; `beta` in prior topology? prior independent of beta.
This file doesn't postulate an identification of analytic formulas with
these values. It is a usable exact normalization interface. Restriction to
subset of slots even with repeated locations uses Names (cannot allow a
pair that your larger family's actual Census didn't test without another
comparison). No inferring analytic denominator bounds on complex offsets
from the qualitative lower positivity here. Gauge algebra regular rotations
used earlier were not transformations of prior; no Jacobian there.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Law
open Lattice Wilson RG Marker Overlay Function Filter MeasureTheory Finset Extra.Trajectories
open RG3.Forms
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} (hC : C.Makes)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {N p : ℕ} (q : Probes C V N p)
variable (j : ℕ)

def fineModel (R : Census V) (U : Config G (C.side j p)) :=
  Poly.inject fun x : R.Mode => q.toInsertions.total x j (matrixField U)

def coarseRatio (R : Census V) (U : Config G (C.side j p)) :=
  q.toInsertions.ratios R j (matrixField U)

def denom (U : Config G (C.side j p)) := Insertions.vacuum C.path N p j (matrixField U) -- N variable not bound!
variable {j}
lemma denom_positive (hj : j ≤ N) (U : Config G (C.side j p)) : 0 < denom (C:=C) (N:=N) j U := Insertions.vac_pos hj _
include hC in
lemma denom_eq (hj : j ≤ N) (U : Config G (C.side j p)) : denom (C:=C) (N:=N) j U=(C.path.rep N p j).eval U := congrFun (Insertions.vac_eq hC.wilson hj) U
include hC in
lemma common (hj : j<N) (U : Config G (C.side j p)) :
    denom (C:=C) (N:=N) j U = ∫ V : Config G (C.side (j+1) p),
      (C.path.levels.clock.op j p).density (C.path.β N p (j+1)) V U * (C.path.rep N p (j+1)).eval V ∂prior G _ := by
  rw [denom_eq hC hj.le U,(hC.wilson.steps N p j hj).1]; rfl

omit [Fintype V] in
lemma vac (hj : j≤N) (U) : (fineModel q j R U).part R.quiet = (denom (C:=C) (N:=N) j U:ℂ) := by
  rw [fineModel]; exact congrFun (q.toInsertions.quiet_eq hj) _
omit [Fintype V] in
lemma scaler_of (U : Config G (C.side j p)) (i : R.Mode) :
    (coarseRatio q j R U).part i = (fineModel q j R U).part i * (↑((denom (C:=C) (N:=N) j U)⁻¹) : ℂ) := rfl
omit [Fintype V] in
lemma at_top (U : Config G (C.side N p)) (i:R.Mode) :
    (fineModel q N R U).part i = Ride.bump (C.S.a N) i q.d * (bare (C.beta N p) U : ℂ) * ∏ a∈i.val, q.eval a U := by
  change q.toInsertions.total i N _=_
  rw [Insertions.total_top,Insertions.source_eq]
  simp_rw [Ride.Product,← q.physical]
  rfl
omit [Fintype V] in
lemma passing (hj : j<N) (U : Config G (C.side j p)) (i:R.Mode) :
    (fineModel q j R U).part i = Ride.bump ((C.S.block j).val:ℝ) i q.d *
      (C.path.levels.clock.op j p).push (C.path.β N p (j+1)) (fun V => (fineModel q (j+1) R V).part i) U := by
  change q.toInsertions.total i j _=_; rw [Insertions.total_step q.toInsertions i j hj]
  exact congrArg (Ride.bump ((C.S.block j).val:ℝ) i q.d * ·) (Insertions.step_push j (q.toInsertions.smooth_total i hj).continuous _)

-- Input/output Deck P needn't have been the issued Rep definitionally!
-- Always require exact numerator and preserve separately with Eq receipts
-- over Deck, transport back to H.rep via `q.toInsertions` etc. P lawful is
-- a separate receipt and estimate. This minimalist consumer doesn't try to
-- identify vac beta/path; always keep other receipts for calling producer
-- with H labels.
def Checked {P : Rep G (C.side j p)} (d : Deck R P) := ∀ U,d.density U=fineModel q j R U

lemma same_pure {P Q : Rep G (C.side j p)} (d : Deck R P) (e : Deck R Q) (h : Checked q d)
    (he : d.density=e.density) : Checked q e := fun U => (congrFun he U).symm.trans (h U)

lemma integrable_deck {P : Rep G (C.side j p)} (d : Deck R P) (h : d.Active) {Θ r s t b a}
    (he : d.Budget Θ r s t b a) {σ C0 Λ δ u} (hp : P.Lawful σ C0 Λ δ u) :
    Integrable d.density (prior G _) := by
  obtain ⟨hm,B,h⟩ := d.envelope h he hp
  exact Integrable.of_bound hm.aestronglyMeasurable B (Eventually.of_forall h)

lemma get (hj : j<N) {P : Rep G (C.side (j+1) p)} (d : Deck R P)
    (h : Checked q d) (hb : d.Active) {Θ r s t b a} (he : d.Budget Θ r s t b a) {σ C0 Λ δ u} (hp : P.Lawful σ C0 Λ δ u)
    (U : Config G (C.side j p)) (i:R.Mode) :
    (fineModel q j R U).part i = Ride.bump ((C.S.block j).val:ℝ) i q.d * ((C.path.levels.clock.op j p).push (C.path.β N p (j+1)) d.density U).part i := by
  rw [passing q hj U i]
  have H' := MergeProof.Accent.push_get (C.path.levels.transition_mass _ _ (C.path.β N p (j+1))) (integrable_deck d hb he hp) i
  unfold Checked at h
  exact congrArg (Ride.bump ((C.S.block j).val:ℝ) i q.d * ·) (by simp_rw [← h]; exact (congrFun H' U).symm)

-- Numerator and denominator AND connected version, pointwise on full V,
-- true ordinary coefficients before log. `ratio` uses dimension factors with
-- EVERY selection including singleton and Fiber and no implicit inverse
-- transfer of scalars. Relative to unnorm probability Haar; noise/per-tag
-- probabilities included in StepData.density fine-first. Preserve d if
-- replacing by `Forms.Test.stay` or `produce` via same_pure.
include hC in
theorem normalized (hj : j<N) {Q : Rep G (C.side (j+1) p)} (d : Deck R Q)
    (h : Checked q d) (hb : d.Active) {Θ r s t b a} (he : d.Budget Θ r s t b a) {σ C0 Λ δ u} (hp : Q.Lawful σ C0 Λ δ u)
    (U : Config G (C.side j p)) :
    let S := C.path.levels.clock.op j p
    let beta := C.path.β N p (j+1)
    let den := ∫ V : Config G (C.side (j+1) p), S.density beta V U * (C.path.rep N p (j+1)).eval V ∂prior G _
    let num := Poly.inject (fun i:R.Mode => Ride.bump ((C.S.block j).val:ℝ) i q.d * (S.push beta d.density U).part i)
    0 < den ∧ fineModel q j R U=num ∧ coarseRatio q j R U=(↑(den⁻¹):ℂ) • num ∧
      ∀ i : R.Mode, q.toInsertions.cumulant j i (matrixField U)= (connected ((↑(den⁻¹):ℂ) • num)).part i := by
  intro S beta den num
  have hx : denom (C:=C) (N:=N) j U=den := common hC hj U
  have hnum : fineModel q j R U=num := Marker.Poly.ext (get q hj d h hb he hp U)
  have hratio : coarseRatio q j R U=(↑(den⁻¹):ℂ) • num := by
    apply Marker.Poly.ext; intro i
    rw [scaler_of,hx,show fineModel q j R U=num from hnum,Poly.part_smul,mul_comm]
  exact ⟨hx ▸ denom_positive hj.le U,hnum,hratio,fun i => congrArg (fun a => (connected a).part i) hratio⟩

-- same checked law after `StepData.push`, with explicit preservation of
-- scalar still proved *on the history*, not assumed as phase identifier.
theorem checked_next (hj : j<N) {Q : Rep G (C.side (j+1) p)} (d : Deck R Q)
    (h : Checked q d) (hb : d.Active) {Θ r s t b a} (he : d.Budget Θ r s t b a) {σ C0 Λ δ u} (hp : Q.Lawful σ C0 Λ δ u)
    {P : Rep G (C.side j p)} (e : Deck R P)
    (HG : ∀ U i,(e.density U).part i=Ride.bump ((C.S.block j).val:ℝ) i q.d*
      ((C.path.levels.clock.op j p).push (C.path.β N p (j+1)) d.density U).part i) : Checked q e := fun U => Marker.Poly.ext (fun i => (HG U i).trans (get q hj d h hb he hp U i).symm)
end YM.RG3.Law
