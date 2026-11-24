import YM.FormalBulk08.Orb.Kuttle

/-! Jacobian constant normalized on the unshifted slice. This is always before
per-site Gaussian determinant terms are considered (no extensive normalization). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Matrix PowerSeries
open scoped BigOperators
variable {V J I : Type*}
variable [DecidableEq V] [Fintype V]
omit [DecidableEq V] [Fintype V] in
lemma shaft_boost (q : Pap I) (i : V) : shaft (MvPolynomial.pderiv i) (boost V q)=0 := by ext1 n; simp [boost]
variable (H D : Hull V I)
variable (Y : V→Pap (V⊕J)) (z w : I→Pap J)
variable [Fintype J] (L M : Matrix V V ℝ)

def inset : Matrix V V (Pap (V⊕J)):= Matrix.of fun i j=>shaft (MvPolynomial.pderiv (Sum.inl j)) (Y i)
def gauche : Pap (V⊕J):=C (MvPolynomial.C M.det) * (inset Y).det

def glide (L : Matrix V V ℝ) (Z : V→ Glyphs ℝ J) : V→Glyphs ℝ (V⊕J) := fun i=> MvPolynomial.rename Sum.inl (mixRows L (MvPolynomial.X i))+ MvPolynomial.rename Sum.inr (Z i)

lemma wing (p : Pap (V⊕J)) (i : V) : shuttle H z (shaft (MvPolynomial.pderiv (Sum.inl i)) p)=shaft (MvPolynomial.pderiv i) (shuttle H z p) := by
   classical
   unfold shuttle levels roam
   let P:= fun j:J=>boost V (C (MvPolynomial.X j : TypeR J))
   let A:=Sum.elim (live H z) P
   let D: Derivation (TypeR J) (Glyphs (TypeR J) V) (Glyphs (TypeR J) V):=MvPolynomial.pderiv i
   have ht (U) : shaft D U=shaft (D.restrictScalars ℝ) U := rfl
   have he (a:V⊕J) : shaft (D.restrictScalars ℝ) (A a)= if a=Sum.inl i then 1 else 0 := by
      rw [←ht]
      cases a with
      | inl u=>
        change shaft D (C _+boost _ _) = _; rw [map_add,shaft_boost,shaft_C,add_zero];
        by_cases h:u=i
        · subst u; simp [D]
        simp [D,h]
      | inr u=> change shaft D (boost _ _)=_; simp [shaft_boost,D]
   change _=shaft D (changeBy (insertAt ℝ A) p); rw [ht,diff_chain]; simp_rw [he,mul_ite,mul_one,mul_zero]; rw [Finset.sum_ite_eq']; simp; rfl

lemma gauge_factor : shuttle H z (gauche Y M)=jac (centered H D Y z w) (MvPolynomial.C.mapMatrix M) := by
   unfold gauche jac
   rw [map_mul];
   have hh (r:ℝ) : shuttle H z (C (MvPolynomial.C r))=C (MvPolynomial.C (MvPolynomial.C r)) := by simp [shuttle,levels,roam]
   rw [hh,←RingHom.map_det,RingHom.map_det]
   have he : (shuttle H z) (inset Y).det=(clock (centered H D Y z w)).det := by
      rw [RingHom.map_det, show (shuttle H z).mapMatrix (inset Y)=_ from ?hb]
      case hb => ext1 i j; change shuttle H z (shaft (MvPolynomial.pderiv (Sum.inl j)) (Y i))=shaft (MvPolynomial.pderiv j) (centered H D Y z w i); rw [centered,map_sub,shaft_boost,sub_zero]; exact wing H z _ _ -- transparency
   rw [he]

omit [Fintype J] in
lemma wing_level (h : ∃ Z, ∀ i,coeff 0 (Y i)=glide L (V:=V) Z i) : ∃ Z:V→TypeR J, ∀ i,coeff 0 (centered H D Y z w i)= tilt Z (MvPolynomial.C.mapMatrix L) i := by
   obtain ⟨Z,hZ⟩ := h
   let v (i:V) := coeff 0 (roam ℝ z (C (H.drift i))); let v' (i:V):=coeff 0 (roam ℝ w (C (D.drift i)))
   let m (i:V):=∑ j,MvPolynomial.C (L i j)*v j
   refine ⟨fun i=>m i+Z i-v' i,fun i=>?_⟩
   let A:= Sum.elim (live H z) (fun i:J=>boost V (C (MvPolynomial.X i)))
   have he : coeff 0 (shuttle H z (Y i))=coeff 0 (levels (live H z) (C (glide L Z i))) := by
      change coeff 0 (changeBy _ _)= coeff 0 (changeBy (insertAt ℝ A) _); rw [change_coeff_zero,change_coeff_zero,hZ,coeff_zero_C]
   rw [centered,map_sub,he,levels,roam_level]
   have hh (p:Glyphs ℝ J): MvPolynomial.aeval (fun i=>coeff 0 (A i)) (MvPolynomial.rename Sum.inr p) = MvPolynomial.C p := by
      induction p using MvPolynomial.induction_on with
      | C c=> simp [A]
      | add p g hp hg=> simp_rw [map_add,hp,hg]
      | mul_X p i hp=> simp_rw [map_mul,MvPolynomial.rename_X,MvPolynomial.aeval_X,hp]; simp [A,boost]
   rw [glide,map_add, hh]; simp [live,advance,boost,tilt,mixRows,v,v',m,mul_add,Finset.sum_add_distrib]; simp_rw [←coeff_zero_eq_constantCoeff_apply, coeff_map]; abel
omit [Fintype J] in
lemma gauche_unit (h : ∃ Z, ∀ i,coeff 0 (Y i)=glide L Z i) (hM : L*M=1) : coeff 0 (gauche Y M)=1 := by
   rw [gauche,coeff_C_mul,coeff_zero_eq_constantCoeff_apply]; obtain ⟨Z,hZ⟩:=h
   have he (i j : V) : constantCoeff (shaft (MvPolynomial.pderiv (Sum.inl j)) (Y i))=MvPolynomial.C (L i j) := by
     rw [←coeff_zero_eq_constantCoeff_apply,coeff_shaft,hZ,glide,map_add,MvPolynomial.pderiv_rename Sum.inl_injective]
     have ht (p : Glyphs ℝ J) : MvPolynomial.pderiv (Sum.inl j) (MvPolynomial.rename Sum.inr p)=0 := by
        induction p using MvPolynomial.induction_on <;> simp_all
     rw [ht,add_zero, show mixRows L (MvPolynomial.X i)= tilt (fun _=>0) L i from by simp [tilt_eq],tilt_grad];simp
   have h : constantCoeff (inset Y).det=MvPolynomial.C L.det := by
       rw [RingHom.map_det,show constantCoeff.mapMatrix (inset Y) = MvPolynomial.C.mapMatrix L from ?_ ,←RingHom.map_det]
       ext1 i j; exact he i j
   rw [h,←map_mul,←Matrix.det_mul,mul_eq_one_comm.mp hM,Matrix.det_one,map_one]
lemma comparison (p t : Pap (V⊕I)) (Q : L*M=1) (h : ∃ Z, ∀ i,coeff 0 (Y i)=glide L Z i)
     (E : dish (still V J) z p=dish Y w t + covelog (gauche Y M)) :
   Elan H D p t z w (centered H D Y z w) (MvPolynomial.C.mapMatrix L) (MvPolynomial.C.mapMatrix M) := by
    refine ⟨by rw [←map_mul,Q,map_one], wing_level H D Y z w L h,?_⟩
    rw [←lease,E,map_add,discount,←gauge_factor]
    exact congr_arg (_ + ·) (change_covelog _ (gauche_unit Y L M h Q))
end YM.FormalBulk08.Orb
