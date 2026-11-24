import YM.FormalBulk08.Orb.Triplet

/-! Equal legs under formal Jacobian transformation. Includes induced external e0-derived
positive-order changes in action (gauge differences usually alter those). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Matrix PowerSeries
open scoped BigOperators
variable {V I J : Type*} [DecidableEq V] [Fintype V]
variable (H D : Hull V I) (p t : Pap (V ⊕ I)) (hp : Solved H p) (ht : Solved D t) (z w : I→Pap J) (y : V→Ink V J)
-- L in ring with external parameters
variable (L M : Matrix V V (TypeR J))
def jac := C (MvPolynomial.C M.det)*(clock y).det
structure Elan : Prop where
   invert : L*M=1
   origin : ∃ Z:V→TypeR J, ∀ i,coeff 0 (y i)=tilt Z L i
   speech : roam ℝ (advance H z) p = roam (TypeR J) y (roam ℝ (advance D w) t)+covelog (jac y M)

lemma weight_jac (h : ∃ Z:V→TypeR J, ∀ i,coeff 0 (y i)=tilt Z L i) (hm : L*M=1) : coeff 0 (jac y M)=1 := by
   rw [jac,coeff_C_mul,coeff_zero_eq_constantCoeff_apply]
   have he : PowerSeries.constantCoeff.mapMatrix (clock y) = MvPolynomial.C.mapMatrix L := by
     obtain ⟨Z,hZ⟩:= h; ext1 i j; change PowerSeries.constantCoeff (shaft (MvPolynomial.pderiv j) (y i))=MvPolynomial.C _
     rw [←coeff_zero_eq_constantCoeff_apply,coeff_shaft,hZ,tilt_grad]
   have hh : constantCoeff ((clock y).det)= MvPolynomial.C L.det := by rw [RingHom.map_det,he,←RingHom.map_det]
   rw [hh,←map_mul,←Matrix.det_mul,mul_eq_one_comm.mp hm,Matrix.det_one,map_one]

variable (Q : Elan H D p t z w y L M)
-- normal order0 of teleported series
omit [DecidableEq V] [Fintype V] in
lemma stripped {F : Ink V I} (q : coeff 0 F=0) : coeff 0 (teleport z F)=0 := by rw [teleport,change_coeff_zero,q,map_zero,map_zero]
lemma grade {U W R : Type*} [CommRing R]
   (b : W→ Plate R U) {f : Plate R W} (h : coeff 0 f=0) : coeff 0 (roam R b f)=0 := by rw [roam,change_coeff_zero,h,map_zero,map_zero]
lemma rode {I U : Type*} {b : I→Pap U} {p : Pap I}(h : coeff 0 p=1) : coeff 0 (roam ℝ b p)=1 := by rw [roam,change_coeff_zero,h,map_one,coeff_zero_one]

section
include Q
lemma central_view : C (variation H.saddle J).base+boost V (roam ℝ z (C H.main))+teleport z (positive H p) =
    roam (TypeR J) y (C (variation D.saddle J).base)+boost V (roam ℝ w (C D.main))+roam (TypeR J) y (teleport w (positive D t))+covelog (jac y M) := by
   have he:=Q.speech; rw [←teleport_toInk,←teleport_toInk, positive_eq H, positive_eq D] at he; simp_rw [map_add,teleport_boost,teleport_base,roam_boost] at he; exact he

include hp ht
lemma principal_view : Lᵀ*(variation D.saddle J).P*L=(variation H.saddle J).P ∧
     (∀ i,coeff 0 (y i)= mixRows L (MvPolynomial.X i)) ∧ coeff 0 (roam ℝ z (C H.main))=coeff 0 (roam ℝ w (C D.main)) := by
   have he:=central_view H D p t z w y L M Q; obtain ⟨Z,hZ⟩:=Q.origin
   have hv:=congr_arg (coeff 0) he; simp_rw [map_add,stripped z (plur H p hp),grade _ (stripped w (plur D t ht)),covelog_rank (weight_jac y L M Q.origin Q.invert), add_zero] at hv
   unfold boost at hv; simp_rw [roam_level,hZ,coeff_map, coeff_zero_C] at hv
   obtain ⟨hR,h0,h⟩:= oar _ _ L M Z _ _ Q.invert hv
   refine ⟨hR,fun i=> ?_, h⟩; rw [hZ,h0]; simp [tilt_eq]

lemma leaf_equal (F G : Ink V J) (h : F = roam (TypeR J) y G) :
     let a:=roam ℝ w (C D.main) - roam ℝ z (C H.main)
     beam (variation H.saddle J).call (expan (teleport z (positive H p))*F)=
       expan a * beam (variation D.saddle J).call (expan (teleport w (positive D t))*G) := by
   intro a; let A:=teleport z (positive H p); let B:=teleport w (positive D t); let T:=variation H.saddle J; let U:=variation D.saddle J
   obtain ⟨hU,hy,hc⟩:= principal_view H D p t hp ht z w y L M Q
   have e := pivot L M T U (expan B * G) y hU Q.invert (mul_eq_one_comm.mp Q.invert) hy
   let Δ:= roam (TypeR J) y (C U.base)-C T.base; let j:=covelog (jac y M);
   have he:=central_view H D p t z w y L M Q
   have ha : A = boost V a+Δ+roam (TypeR J) y B+j := by
     unfold a Δ; rw [map_sub]; apply add_left_cancel (a:=C T.base+boost V (roam ℝ z (C H.main)))
     rw [he]; change _+roam _ _ B+j=_; abel
   have hB : coeff 0 B=0 := stripped w (plur D t ht); have hA : coeff 0 A=0 := stripped z (plur H p hp)
   have hG:=grade y hB; have hJ:= weight_jac y L M Q.origin Q.invert; have hj : coeff 0 j=0 := covelog_rank hJ
   have hb : coeff 0 a=0 := by unfold a; rw [map_sub,hc,sub_self]
   have hd : coeff 0 (boost V a)=0 := by rw [boost,coeff_map,hb,map_zero]
   have hh : coeff 0 Δ=0 := by rw [ha] at hA; simp_rw [map_add,hj,hG,hd,zero_add,add_zero] at hA; exact hA
   have hm : beam T.call (expan A*F)=C M.det * (expan a * (C L.det * beam U.call (expan B*G))) := by
     rw [←e,map_mul (roam (TypeR J) y), show roam (TypeR J) y (expan B)=expan (roam (TypeR J) y B) from change_expan _ hB,ha,←expan_mul (by rw [map_add,map_add,hd,hh,hG,zero_add,zero_add]) hj,
       ←expan_mul (by rw [map_add,hd,hh,zero_add]) hG,←expan_mul hd hh,show expan j=jac y M from expan_after hJ, show expan (boost V a) = boost V (expan a) from (map_expan MvPolynomial.C hb).symm]
     rw [← suction H.saddle, ← beam_swing T]; apply congr_arg (beam T.call)
     rw [h]; unfold jac Δ; ring
   rw [hm]; rw [mul_left_comm, ←mul_assoc (C M.det),←map_mul,←Matrix.det_mul, mul_eq_one_comm.mp Q.invert, Matrix.det_one,map_one,one_mul]
end
end YM.FormalBulk08.Orb

namespace YM.FormalBulk08.Orb
open Series Wick Matrix PowerSeries
open scoped BigOperators
variable {V I J : Type*} [DecidableEq V] [Fintype V]
variable (H D : Hull V I) (p t : Pap (V ⊕ I)) (hp : Solved H p) (ht : Solved D t) (z w : I→Pap J) (y : V→Ink V J)
variable (L M : Matrix V V (TypeR J)) (Q : Elan H D p t z w y L M)
include Q hp ht
lemma voice_carry : roam ℝ z (vocal H p)=expan (roam ℝ w (C D.main)-roam ℝ z (C H.main))*roam ℝ w (vocal D t) := by
   have hh:= leaf_equal H D p t hp ht z w y L M Q 1 1 (map_one _).symm
   dsimp only at hh; rw [mul_one,mul_one] at hh
   unfold vocal; simp_rw [←vacuum_commutes];
   have h : teleport z (expan (positive H p))=expan (teleport z (positive H p)):=change_expan _ (plur H p hp)
   have e : teleport w (expan (positive D t))=expan (teleport w (positive D t)):=change_expan _ (plur D t ht)
   rw [h,e]; exact hh

theorem action_view : roam ℝ z (out H p)=roam ℝ w (out D t) := by
   have h:=voice_carry H D p t hp ht z w y L M Q
   let a:=roam ℝ w (C D.main)-roam ℝ z (C H.main)
   have hg := (principal_view H D p t hp ht z w y L M Q).2.2
   have he : coeff 0 a=0 := by unfold a; rw [map_sub,hg,sub_self]
   have hy : coeff 0 (roam ℝ w (vocal D t))=1 := rode (voice D t ht)
   change _ = expan a*_ at h
   rw [← expan_after hy] at h -- pattern issue
   unfold out; rw [map_add,map_add,show roam ℝ z (covelog (vocal H p))=covelog (roam ℝ z (vocal H p)) from change_covelog _ (voice H p hp),h]
   rw [expan_mul he (covelog_rank hy), covelog_after (by rw [map_add,covelog_rank hy,he,zero_add]), show roam ℝ w (covelog (vocal D t))= covelog (roam ℝ w (vocal D t)) from change_covelog _ (voice D t ht)];unfold a; abel

theorem mark_view (U F : Pap (V ⊕ I)) (h : roam ℝ (advance H z) U=roam (TypeR J) y (roam ℝ (advance D w) F)) : roam ℝ z (flag H p U)=roam ℝ w (flag D t F) := by
    have hh := leaf_equal H D p t hp ht z w y L M Q (roam ℝ (advance H z) U) (roam ℝ (advance D w) F) h
    let A:=roam ℝ z (vocal H p)
    apply (IsUnit.mul_right_inj (a:=A) ?_).mp
    · dsimp only [A]; rw [←map_mul,normalization _ _ hp, ←vacuum_commutes,map_mul, teleport_toInk]
      rw [show teleport z (expan (positive H p))=expan (teleport z (positive H p)) from change_expan _ (plur H p hp),hh, voice_carry H D p t hp ht z w y L M Q,mul_assoc,←map_mul (roam ℝ w),normalization _ _ ht,←vacuum_commutes,map_mul (teleport w),teleport_toInk,
      show teleport w (expan (positive D t))=expan (teleport w (positive D t)) from change_expan _ (plur D t ht)]
    apply isUnit_iff_constantCoeff.mpr; rw [←coeff_zero_eq_constantCoeff_apply, rode (p:=vocal H p) (voice H p hp)]; exact isUnit_one -- A
end YM.FormalBulk08.Orb
