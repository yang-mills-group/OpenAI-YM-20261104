import YM.OPE.Orbits.System
import YM.OPE.Detector

/-!
Bind the finite physical detector to the complete-product and packet
readouts of the original orbit Reader. The insertion center is explicitly
zero, matching `witnessAt`; no translation or frame change is implicit.
The finite-enumeration proof follows the existing `Readout05.Report.cafes`
calculation without importing its unrelated analytic supplier closure.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Function Spec OPE OPE.Orbits Table
open scoped Classical BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S)

include F in
private theorem detector_finite_moment {I : Type} [Fintype I] {d : I → ℕ}
    (v : Labels S d) (n : ℕ) (e : Fin n ≃ I) (x : Points n) (hx : x ∈ conf n)
    (L : I → E4) (he : L ∘ e = x.ofLp) :
    S.useAt S x (Orbits.tags v ∘ e) = Orbits.moment S L v := by
  have hL : Injective L := by
    rw [← Function.comp_id L, ← e.self_comp_symm, ← Function.comp_assoc, he]
    exact (show Injective x.ofLp from hx).comp e.symm.injective
  rw [observed, ← perm_observe S F.room.kernel.laws.toSymmetric e (names v) hL,
    he, named_fin S F.room.kernel.laws.toSymmetric _ hx,
    ← S.at_project S F.room.kernel.laws.toSymmetric (fun _ => le_rfl) hx]
  apply congr_arg
  funext i
  change (⟨_, v (e i)⟩ : S.Tag) = ⟨_, S.project _ (S.representative _ (v (e i)))⟩
  rw [S.rep]

include F in
/-- The actual finite detector's scalar is the orbit Reader's single-field
readout at the same origin, exterior positions and exterior fields. -/
theorem detector_witness_eq_upon {D : ℕ} (E : OPE.ExteriorData S)
    (hE : OPE.Apt E) (z : S.Field D) :
    OPE.witnessAt S D E z =
      Orbits.upon S D 0 (OPE.positions S E).ofLp
        (e := fun i => (OPE.tags S E i).1) (fun i => (OPE.tags S E i).2) z := by
  rw [OPE.witness_kernel]
  let w := OPE.tags S E
  let y := OPE.positions S E
  let v : Labels S (fun _ : Unit => D) := sole z
  let a := stages v (f := fun i => (w i).1) (fun i => (w i).2)
  let e : Unit ⊕ Fin E.length ≃ Fin (E.length + 1) :=
    { toFun := Sum.elim (fun _ => 0) Fin.succ
      invFun := Fin.cases (.inl ()) Sum.inr
      left_inv := by intro i; cases i <;> simp
      right_inv := by intro i; refine Fin.cases ?_ (fun j => ?_) i <;> simp }
  change S.useAt S (Points.cons 0 y) (Fin.cons ⟨D,z⟩ w) =
    Orbits.moment S (beside (sole 0) y.ofLp) a
  rw [show Fin.cons ⟨D,z⟩ w = Orbits.tags a ∘ e.symm from by
    funext i
    obtain ⟨i, rfl⟩ := e.surjective i
    rw [comp_apply, e.symm_apply_apply]
    cases i with
    | inl i => rfl
    | inr i => exact Fin.cons_succ ..]
  apply detector_finite_moment F a _ e.symm _ (generic_conf _ hE)
  funext i
  obtain ⟨i, rfl⟩ := e.surjective i
  rw [comp_apply, e.symm_apply_apply]
  cases i <;> rfl

private theorem detector_origin_separated (E : OPE.ExteriorData S) (hE : OPE.Apt E) :
    Injective (beside (sole (0 : E4)) (OPE.positions S E).ofLp) := by
  have h := generic_conf _ hE
  intro i j hij
  cases i with
  | inl i =>
    cases j with
    | inl j => rfl
    | inr j =>
      have he : (0 : Fin (E.length+1)) = j.succ := h hij
      exact (Fin.succ_ne_zero j he.symm).elim
  | inr i =>
    cases j with
    | inl j =>
      have he : i.succ = (0 : Fin (E.length+1)) := h hij
      exact (Fin.succ_ne_zero i he).elim
    | inr j =>
      have he : i.succ = j.succ := h hij
      exact congrArg Sum.inr (Fin.succ_injective _ he)

variable (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {I : Type} [Fintype I] {d : I → ℕ}

/-- The first finite-detector residual is exactly the existing ordinary
OPE remainder on the complete physical product, with no changed fields. -/
theorem detector_packet_residual (D : ℕ) (x : I → E4) (v : Labels S d)
    (E : OPE.ExteriorData S) (hE : OPE.Apt E) :
    Orbits.whole S x v (OPE.positions S E).ofLp
        (e := fun i => (OPE.tags S E i).1) (fun i => (OPE.tags S E i).2) -
      OPE.witnessAt S D E (R.packet D x v 0) =
      Orbits.formula F R x 0 v (OPE.positions S E).ofLp
        (e := fun i => (OPE.tags S E i).1) (fun i => (OPE.tags S E i).2) D none := by
  rw [detector_witness_eq_upon F E hE]
  unfold Orbits.formula
  rw [← Orbits.packet_read F R x 0 v (OPE.positions S E).ofLp
    (fun i => (OPE.tags S E i).2) none D (detector_origin_separated E hE)]
  rfl

end YM.Integration
