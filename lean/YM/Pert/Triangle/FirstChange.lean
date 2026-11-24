import YM.Pert.Triangle.Inert
import YM.Pert.Triangle.WickParity
import YM.Pert.Parity.EvenLow
import YM.Pert.Triangle.Diagnostic

/-! No first-order variation from a regular filtration-preserving redefinition of
the labels in this triangle. This is for the continuum Maxwell leading tensors.
It does *not* estimate lattice terms times possibly divergent bare mixing matrices. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 450000
noncomputable section

namespace YM.Pert.Triangle
open Maxwell Analysis Function Set Wick Parity Labels RawLabels Lattice UVNext.FreeStress Extra.FD
variable {G:Gauge} (hg:G.Simple) (F:Frames G)
lemma enroll_write (n:ℕ) (u:Label G n) : writes F n (enroll F n u) = reduceEq u.val := by
  unfold enroll embed; rw [LinearMap.comp_apply,writes_project]
  change reduceEq (((F.level n).coords.symm ((F.level n).coords u)).val) = _
  rw [LinearEquiv.symm_apply_apply]
lemma writes_through (n:ℕ) (p:(freeTable F).Field n) : writes F n p ∈ through G n := by
  obtain ⟨q,rfl⟩ := covers F p
  rw [show writes F n (embed F n q) = _ from enroll_write F ..]
  exact filterMove generation costKey (reduceEq (G:=G)) (gradientReduce (fun i=>i+2)) (hp:=q.property.1)

include hg in
lemma low_reversal {v : (freeTable F).Field 6} (ht : v∈Position.lower F 4 6) :
    reversePol G (writes F _ v) = writes F 6 v := by
  obtain ⟨⟨p,hp⟩,rfl⟩ := ht
  rw [LinearMap.comp_apply]; simp only [enroll_write]
  change reversePol G (reduceEq (⟨p,hp.1⟩:Label G 4).val)=reduceEq p
  rw [←reversal_raw, ←show (wash G 4 ⟨_,hp.1⟩).val=shadow G p from rfl, wash_four hg,LinearMap.id_apply]
lemma odd_reversed : reversePol G (writes F 6 ((basic F) 0)) = -(writes F 6 (basic F 0)) := by
  have h := enroll_write F 6 (sent (G:=G) 0)
  change reversePol G (writes F 6 (enroll F 6 (sent 0)))= -writes F 6 (enroll F 6 _)
  rw [h, sent,if_pos rfl,← reversal_raw, show shadow G (oddSlot G).val = (wash G 6 (oddSlot G)).val from rfl,bFan_sign]
  change reduceEq (-(bFan G)) = -reduceEq (bFan G); exact map_neg .. 
lemma lower_basic (i:Fin 3) (hi:i≠0) : basic F i ∈ Position.lower F 4 6 :=
    ⟨⟨uMinus G,(evenSlot G).property,(raiseLabel G (show 4≤6 by decide) (evenSlot G)).property⟩,by unfold basic; simp only [comp_apply,sent,if_neg hi]; rfl⟩
lemma write_minus (i:Fin 3) (hi:i≠0) :
    writes F 6 (basic F i)= reduceEq (uMinus G) := by
  unfold basic; simp only [comp_apply,sent,if_neg hi]; exact enroll_write ..

variable {x:Points 3} (hx : x ∈ conf 3)
include hg hx
lemma ordinary_kills (D : Fin 3 → WickPol G)
 (hD : D 0∈through G 6) (hM : ∀i:Fin 3, i≠0 → reversePol G (D i) = D i)
 (hU:∀i:Fin 3, i≠0 → D i=reduceEq (uMinus G)) : Wick.moment G x D=0 := by
  -- just first-shift test
  rw [show D = triangle (D 0) (reduceEq (uMinus G)) (reduceEq (uMinus G)) from (by ext i; fin_cases i <;> simp [hU])]
  exact shift_at_outer hx hD
lemma ordinary_kills_even (D : Fin 3 → WickPol G)
 (h : D 0 = writes F 6 (basic F 0)) (hM : ∀i:Fin 3, i≠0 → reversePol G (D i) = D i) :
    Wick.moment G x D=0 := by
    let q : Fin 3→ℂ := fun i=> if i=0 then -1 else 1
    have he : reversePol G ∘ D = fun i:Fin 3=> q i • D i := funext fun i=> by by_cases hi:i=0; subst i; rw [comp_apply,h,odd_reversed]; simp [q]; simpa only [comp_apply,q,if_neg hi, one_smul] using hM i hi
    have hq : (∏i,q i)= (-1:ℂ) := by rw [Finset.prod_eq_single_of_mem 0 (Finset.mem_univ _) (fun i _ hi=> if_neg hi)]; exact if_pos rfl
    have h := Wick_flip G x D
    rw [he,MultilinearMap.map_smul_univ,hq, neg_one_smul] at h
    exact minus_id_forces ((neg_one_smul ℝ _).trans h)

theorem free_point_base :
    (freeTable F).useAt (freeTable F) x (fun i:Fin 3=>tag F 6 (sent i))=0 := by
   rw [writes_eval]
   let w(i) := writes F 6 (basic F i)
   change Wick.moment G x w=_
   exact ordinary_kills_even hg F hx w rfl (fun i hi=> low_reversal hg F (lower_basic F i hi))

/-- Free variation in each insertion separately. Only the lower control at weight four for the two U columns is used. Thus no symmetry projection of the bracket-column shift is tacitly presumed. -/
theorem free_point_stability (b : (freeTable F).Field 6 → (freeTable F).Field 6)
  (hb : ∀v∈Position.lower F 4 6,b v ∈ Position.lower F 4 6) (k : Fin 3) :
    (freeTable F).useAt (freeTable F) x (fun i:Fin 3=> Sigma.mk 6 (update (basic F) k (b (basic F k)) i))=0 := by
   rw [writes_eval]
   let D (i:Fin 3) := writes F 6 (update (basic F) k (b (basic F k)) i)
   change Wick.moment G x D=0
   have he (i:Fin 3) (hi:i≠0): reversePol G (D i) = D i := by
     change reversePol G (writes F _ _)=_
     refine low_reversal hg F ?_
     by_cases ht:i=k
     · subst i; rw [update_self]; exact hb _ (lower_basic F k hi)
     rw [update_of_ne ht]; exact lower_basic F i hi
   by_cases h:k=0
   · apply ordinary_kills hg hx D (writes_through F 6 _) he ?_
     intro i hi
     subst k; unfold D
     rw [update_of_ne hi]
     exact write_minus F i hi
   exact ordinary_kills_even hg F hx D (by dsimp [D]; rw [update_of_ne (Ne.symm h)]) he

omit hx in
theorem test_stability (b : Position.Buffer F 6) (f : Test 3) (k:Fin 3) :
    f.applyTo (fun x=>(freeTable F).useAt (freeTable F) x (fun i:Fin 3=> Sigma.mk 6 (update (basic F) k (b.1 (basic F k)) i))) = 0 := by
  apply (YM.Test.apply_eq f (P:=fun _=>0) ?_).trans (by simp [Test.applyTo])
  intro z hz
  exact free_point_stability hg F hz _ (fun u hu=>b.property.2.1 4 (by decide : 4<6) _ hu) k

end YM.Pert.Triangle
