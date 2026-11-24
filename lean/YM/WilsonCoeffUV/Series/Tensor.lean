import Mathlib.Data.Fintype.Perm
import YM.WilsonCoeffUV.Series.Xadic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Ordinary symmetric kernels, with factorial readout. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open MvPolynomial Function
open scoped BigOperators
variable {R U V : Type*} {r t : ℕ}
abbrev Ten (R U:Type*) (r:ℕ) := (Fin r→U) → R
def Smooth (T:Ten R U r) : Prop := ∀ (σ:Equiv.Perm (Fin r)) x, T (x ∘ σ)=T x
lemma Smooth.add [Add R] {P Q:Ten R U r}(h:Smooth P)(e:Smooth Q) : Smooth (P+Q) := by intro s x; simp only [Pi.add_apply,h s x,e s x]
lemma Smooth.zero [Zero R] : Smooth (0:Ten R U r) := fun _ _=>rfl
lemma Smooth.smul {C:Type*}[SMul C R] {P:Ten R U r}(h:Smooth P)(c:C) : Smooth (c•P) := by intro s x; rw [Pi.smul_apply,h s x,Pi.smul_apply]
lemma Smooth.sum [AddCommMonoid R] {I:Type*}{s:Finset I} {p:I→Ten R U r}(h:∀ i∈s,Smooth (p i)) : Smooth (∑ i∈s,p i) := by
  intro σ x; rw [Finset.sum_apply,Finset.sum_apply]; exact Finset.sum_congr rfl fun i hi=>h i hi σ x

def prune (P:Ten R U (r+1))(u:U) : Ten R U r := fun x=>P (Fin.cons u x)
lemma Smooth.prune {P:Ten R U (r+1)} (h:Smooth P)(u:U) : Smooth (prune P u) := by
  intro q x
  let v:= ((finSuccEquiv r).trans (Equiv.optionCongr q)).trans (finSuccEquiv r).symm
  have hx : Fin.cons u (x ∘ q) = Fin.cons u x ∘ v := by
    funext i; refine Fin.cases ?_ (fun j=>?_) i <;> simp [v]
  change P _ = P _; rw [hx,h v _]

def palms [CommSemiring R] [Fintype U] (r : ℕ) : Ten R U r→ₗ[R]MvPolynomial U R where
  toFun T := ∑ i : Fin r→U, T i • ∏ j,X (i j)
  map_add' := fun x y=> by simp [Pi.add_apply,add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

abbrev paint [Fintype U] (r:ℕ) := palms (U:=U) (R:=ℝ) r
-- sym
section sym
variable [AddCommGroup R] [Module ℝ R]
def swirl (P:Ten R U r) : Ten R U r := (Fintype.card (Equiv.Perm (Fin r)):ℝ)⁻¹ • ∑ q:Equiv.Perm (Fin r), fun x=> P (x ∘ q)
lemma swirl_smooth (P:Ten R U r) : Smooth (swirl P) := by
  apply Smooth.smul; intro σ x; rw [Finset.sum_apply,Finset.sum_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun i=>rfl)
lemma swirl_exact {P:Ten R U r} (h:Smooth P) : swirl P=P := by
  funext i; simp_rw [swirl, Pi.smul_apply, Finset.sum_apply, fun y=>h y i,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (R:=ℝ),smul_smul,inv_mul_cancel₀,one_smul]; exact_mod_cast (Fintype.card_pos (α:=Equiv.Perm (Fin r))).ne'
lemma swirl_sum {I:Type*}(s:Finset I)(P:I→Ten R U r) : swirl (∑ i∈s,P i) = ∑ i∈s,swirl (P i) := by funext x; simp_rw [swirl,Finset.sum_apply,Pi.smul_apply,Finset.sum_apply,Finset.smul_sum]; rw [Finset.sum_comm]
end sym
lemma swirl_paint [Fintype U] (P:Ten ℝ U r) : paint r (swirl P)=paint r P := by
  have he (q:Equiv.Perm (Fin r)) : paint r (fun x=>P (x ∘ q))=paint r P := by
    apply Fintype.sum_equiv (q.symm.arrowCongr (Equiv.refl U))
        (fun i : Fin r→U => P (i ∘ q) • ∏ j,X (i j)) _
    intro i; congr 1
    exact (Fintype.prod_equiv q (fun j=>X (i (q j))) _ (fun j=>rfl)).symm
  simp only [swirl,map_smul,map_sum,he,Finset.sum_const,Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul (R:=ℝ),smul_smul,inv_mul_cancel₀,one_smul]; exact_mod_cast (Fintype.card_pos (α:=Equiv.Perm (Fin r))).ne'
section Semiring
variable [CommSemiring R] [Fintype U]
lemma palm_form (P:Ten R U r) : palms r P=∑ i,P i • ∏ j,X (i j) := rfl
lemma sprouts (P:Ten R U (r+1)) : palms _ P=∑ i : U,X i * palms _ (prune P i) := by
  simp_rw [palm_form]
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1) => U))]
  simp_rw [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  simp only [Fin.prod_univ_succ]; change P (Fin.cons i j) • _ = _
  simp only [Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ]; rw [prune,mul_smul_comm]
omit [Fintype U] [CommSemiring R] in
lemma prune_square {P:Ten R U (r+1+1)} (h:Smooth P)(i j:U) : prune (prune P i) j=prune (prune P j) i := by

  letI:= Classical.decEq U
  let e : Equiv.Perm (Fin (r+1+1)):= Equiv.swap 0 (Fin.succ 0)
  funext x
  have hE : Fin.cons j (Fin.cons i x) ∘ e = Fin.cons i (Fin.cons j x) := by
    funext b; refine Fin.cases (by simp [e]) (fun k=>?_) b
    refine Fin.cases ?_ (fun l=>?_) k
    · rw [Function.comp_apply,Equiv.swap_apply_right]; simp
    rw [Function.comp_apply,Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (fun H=> Fin.succ_ne_zero l (Fin.succ_inj.mp H))]; simp
  rw [prune,prune,prune,prune,←hE,h e _]
lemma shell (P:Ten R U 0) (i:Fin 0→U) : palms 0 P=C (P i) := by
  simp only [palm_form,Fintype.prod_empty,Fintype.sum_unique]; rw [Subsingleton.elim default i,Algebra.smul_def,mul_one,algebraMap_eq]

lemma peel (P:Ten R U (r+1))(h:Smooth P)(i:U) : pderiv i (palms (r+1) P)=(r+1) • palms r (prune P i) := by
  classical
  induction r with
  | zero => rw [sprouts]; simp only [map_sum,pderiv_mul,  (fun Q:Ten R U 0=>shell Q (fun j=>j.elim0)),pderiv_C,mul_zero,add_zero, Nat.zero_add,one_smul]; rw [Finset.sum_eq_single i] <;> simp +contextual
  | succ r ih =>
    calc
    _ = palms _ (prune P i)+∑ j : U,X j*pderiv i (palms _ (prune P j)) := by
      rw [sprouts]; simp_rw [map_sum,pderiv_mul,Finset.sum_add_distrib]; rw [Finset.sum_eq_single i] <;> simp +contextual
    _ = palms _ (prune P i)+(r+1) • (∑ j : U, X j*palms _ (prune (prune P i) j)) := by
      congr 1
      rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun j _=>by rw [ih _ (h.prune j),prune_square h j i,mul_smul_comm])
    _ = _ := by rw [←sprouts,add_smul (r+1) 1,one_smul,add_comm]

def weld (P:Ten R U r)(Q:Ten R U t) : Ten R U (r+t) := fun x=>P (x ∘ Fin.castAdd t)*Q (x ∘ Fin.natAdd r)
private def cleave (r t:ℕ)(U:Type*) : ((Fin r→U)×(Fin t→U)) ≃ (Fin (r+t)→U) where
  toFun x:= Fin.append x.1 x.2
  invFun x:= (x ∘ Fin.castAdd t,x ∘ Fin.natAdd r)
  right_inv := fun x => Fin.append_castAdd_natAdd
  left_inv := fun ⟨x,y⟩=> Prod.ext (funext fun i=>by simp) (funext fun i=>by simp)
lemma palms_weld (P:Ten R U r) (Q:Ten R U t) : palms _ (weld P Q)=palms _ P*palms _ Q := by
  simp_rw [palm_form]; rw [← Equiv.sum_comp (cleave r t U)]
  simp_rw [Fintype.sum_prod_type,Finset.sum_mul,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _
  have h₁ : (cleave r t U) (i,j) ∘ Fin.castAdd t=i:=congr_arg Prod.fst ((cleave r t U).symm_apply_apply (i,j))
  have h₂ : (cleave r t U) (i,j) ∘ Fin.natAdd r=j:=congr_arg Prod.snd ((cleave r t U).symm_apply_apply (i,j))
  rw [weld,h₁,h₂, Fin.prod_univ_add]; simp_rw [Function.comp_def] at h₁ h₂
  simp_rw [congr_fun h₁,congr_fun h₂]; simp [smul_smul, mul_comm]

/-- scalar evaluation at zero -/
lemma scorch (P:Ten R U (r+1)) : eval (0:U→R) (palms _ P)=0 := by rw [sprouts]; simp
lemma toll (P:Ten R U r)(x:U→R) : eval x (palms r P)= ∑ i,P i*∏ j,x (i j) := by simp [palm_form, Algebra.smul_def,eval_mul,algebraMap_eq]
lemma palms_scale [Fintype V] (P:Ten R U r) (M:U→V→R) : aeval (fun i=> ∑ j : V,C (M i j)*X j) (palms r P)= palms r (fun x=>∑ y,P y*∏ i,M (y i) (x i)) := by
  classical
  induction r with
  | zero =>
    let i : Fin 0→V:=fun i=>i.elim0
    rw [shell P default,shell _ i]; simp [algebraMap_eq]
  | succ r ih =>
    rw [sprouts,sprouts]; simp_rw [map_sum,map_mul,ih,aeval_X, Finset.sum_mul]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    let F (j:U) : Ten R V r:= fun x=>∑ y, prune P j y*∏ k,M (y k) (x k)
    change (∑ j,C _*X i*palms r (F j))=X i * _
    suffices h : ∑ j : U,M j i • F j = prune (fun x=>∑ y,P y*∏ k,M (y k) (x k)) i by
      rw [← h,map_sum]; simp_rw [map_smul, Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [Algebra.smul_def,mul_comm _ (X i),mul_assoc,algebraMap_eq]
    funext v; simp_rw [Finset.sum_apply,Pi.smul_apply, smul_eq_mul,F, Finset.mul_sum,prune];
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (r+1) => U)), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro j _; apply Finset.sum_congr rfl; intro x _
    simp only [Fin.consEquiv_apply,Fin.prod_univ_succ, Fin.cons_zero,Fin.cons_succ]; rw [mul_left_comm]; rfl
end Semiring

section Color
variable [Fintype U]

noncomputable def tally : (r:ℕ) → (Fin r→U) → POL U→ₗ[ℝ]ℝ
| 0,_=> (MvPolynomial.aeval (0:U→ℝ)).toLinearMap
| _+1,x=> (tally _ (Fin.tail x)).comp (pderiv (x 0)).toLinearMap
omit [Fintype U] in
lemma tally_zero (P:POL U)(x : Fin 0→U) : tally 0 x P=eval (0:U→ℝ) P := rfl
omit [Fintype U] in
lemma tally_next (P:POL U)(x:Fin (r+1)→U) : tally _ x P=tally _ (Fin.tail x) (pderiv (x 0) P) := rfl
lemma rotate (P:Ten ℝ U r)(h:Smooth P)(x:Fin r→U) : tally r x (paint r P)=r.factorial • P x := by
  induction r with
  | zero => rw [tally_zero,shell P x,eval_C]; simp
  | succ r ih =>
    rw [tally_next,peel P h,map_nsmul,ih _ (h.prune _),prune,Fin.cons_self_tail,Nat.factorial_succ, mul_smul]
lemma pale (h:t≠r)(P:Ten ℝ U t)(hp:Smooth P)(x:Fin r→U) : tally r x (paint t P)=0 := by
  induction t generalizing r with
  | zero => rw [shell P default]; cases r; simp at h; rw [tally_next,pderiv_C,map_zero]
  | succ t ih =>
    cases r with
    | zero=> rw [tally_zero,scorch]
    | succ r=> rw [tally_next,peel P hp,map_nsmul,ih (by omega) _ (hp.prune _) _,smul_zero]
lemma unique_kernel {P Q:Ten ℝ U r} (hp:Smooth P) (hq:Smooth Q)(h:paint r P=paint r Q) : P=Q := funext (fun i=> (smul_right_inj r.factorial_ne_zero).mp (by rw [←rotate P hp i,←rotate Q hq i,h]))

end Color
end YM.WilsonCoeffUV.Blue
