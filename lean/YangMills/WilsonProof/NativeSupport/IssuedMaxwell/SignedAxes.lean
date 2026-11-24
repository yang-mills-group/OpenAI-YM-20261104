import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Reports
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.SignedAxes
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace.Normalize
open scoped Classical BigOperators
variable {g:YangMills.GaugeGroup}{d:ℕ}

theorem jets (s:Signed)(V:TaylorTower g.core)(j:ℕ)(a b:Axis)(v:Fin j→E4):
    (solutionTurn s.ortho⁻¹ (V j)).val a b v=
    (tilt s a * tilt s b) • (V j).val (s.perm a) (s.perm b) (fun i=>Ortho.motion s.ortho (v i)):=by
  change turnJ s.ortho⁻¹ (V j).val a b v=_
  rw [turns_apply]
  simp only [inv_entry,show s.ortho.val=s.matrix from rfl,Signed.matrix_at,inv_inv]
  rw [Finset.sum_eq_single_of_mem (s.perm a) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (s.perm b) (Finset.mem_univ _)]
    · simp only [↓reduceIte,tilt]
      rfl
    intro l _ hl
    simp [Ne.symm hl]
  intro i _ hi
  simp [Ne.symm hi]

theorem original (s:Signed)(p q:Sec g.core d):
    YangMills.Matching.RelatedByAxes (IssuedMaxwell.Reference.issued g) s.perm (tilt s)
      (Ortho.motion s.ortho) p.val q.val ↔ q=ori s.ortho d p:=by
  constructor
  · intro h
    apply Subtype.ext
    apply equalPol
    intro A
    rw [val_ori,reflects_eval]
    exact (h A (fun i=>solutionTurn s.ortho⁻¹ (A i)) (jets s A)).symm
  · rintro rfl V V' h
    have eq:V'=fun j=>solutionTurn s.ortho⁻¹ (V j):=by
      funext j
      apply Subtype.ext
      funext a b
      ext1 v
      exact (h j a b v).trans (jets s V j a b v).symm
    change probe V' p.val=probe V (reflectPol s.ortho p.val)
    rw [reflects_eval,eq]
    rfl
end IssuedMaxwell.SignedAxes
end
