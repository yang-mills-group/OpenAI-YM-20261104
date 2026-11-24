import YM.FormalOPE.RG10.Polarized

/-! From arbitrary-`I` to fixed-horizon `Fin n` coupling ledgers, discarding/reindexing markers
via the common algebra maps. -/

set_option autoImplicit false
noncomputable section

namespace YM.FormalOPE.RG10
open Marker Extra.Trajectories PowerSeries MeasureTheory Filter Finset Word Function
open scoped BigOperators

namespace Polar
variable {V V' I I' : Type} [DecidableEq V] [DecidableEq V'] [DecidableEq I] [DecidableEq I']
    [Fintype V] [Fintype V'] [Fintype I] [Fintype I'] {R : Census V} {S : Census V'}

private lemma image_pay (u : Names R S) (i : I ↪ I') (s : R.Mode) (t : Finset I) :
    ((pay s t).val.image (u.e.sumMap i)) = (pay (u.share s) (t.image i)).val := by
  unfold pay Names.share
  apply Finset.ext; rintro (v|v) <;> simp [Sum.exists]

/-- Preserve allowed subchoices when removing/re-indexing either kind of marker. -/
def nominate (u : Names R S) (i : I ↪ I') : Names (budget R I) (budget S I') where
  e := u.e.sumMap i
  visible s := by rw [← pay_sep s, image_pay]; exact (pay ..).property

lemma share_pay (u : Names R S) (i : I ↪ I') (s : R.Mode) (t : Finset I) :
    (nominate u i).share (pay s t) = pay (u.share s) (t.image i) := Subtype.ext (image_pay ..)

/-- Compatibility under deleting field columns (with identical stencils) and under paying with
different or extra τ's. This is not summing over alternative *stochastic* predictor tags. -/
lemma pays_compatibly (u : Names R S) (i : I ↪ I') (A : Word S) :
    (nominate u i).restriction (certify I' A) = certify I (eraseMarks u A) := by
  ext k; rw [← pay_sep k]
  change (present I' A).part ((nominate u i).share <| pay _ _) = _
  rw [share_pay, certify_present, present_pay, present_pay, card_image_of_injective _ i.injective,
    eraseMarks, coeff_map]; rfl

omit [Fintype V] in
def remain (R : Census V) : Names R R where
  e := Function.Embedding.refl _
  visible s := by change s.val.image id ∈ R.choices; simp

omit [Fintype V] in
@[simp] lemma supports (s : R.Mode) : (remain R).share s = s := Subtype.ext (image_id)

lemma pay_more (e : I ↪ I') (A : Word R) :
    (nominate (remain R) e).restriction (certify I' A) = certify I A := by
  rw [pays_compatibly, show (eraseMarks (remain R)) A = A from observe_ext fun s => by simp]

omit [Fintype I] in
lemma issues (s : Finset I) : ∃ e : Fin s.card ↪ I, Finset.univ.image e = s := by
  let f : (Fin s.card) ≃ ↥s := Fintype.equivOfCardEq (by simp)
  let g : Fin s.card ↪ I := f.toEmbedding.trans (Function.Embedding.subtype (· ∈ s))
  refine ⟨g, Finset.ext fun i => ?_⟩
  rw [mem_image]; constructor
  · rintro ⟨j, -, rfl⟩; exact (f j).property
  intro hi; exact ⟨f.symm ⟨i,hi⟩, mem_univ _, congr_arg Subtype.val (f.apply_symm_apply _)⟩

end Polar
end YM.FormalOPE.RG10
