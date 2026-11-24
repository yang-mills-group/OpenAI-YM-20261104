import YM.SchemeRG11.Cover.Value
import Mathlib.RingTheory.MvPolynomial.Homogeneous
/-! Long line power. Uniform into changing monomial moment. No spike smearing. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Haze
open MvPolynomial Lattice Dose
open scoped Classical
variable {J B I K:Type*}(D:Dose I ℝ)
lemma straights (e:K→I)(p:Finset K)(i:I): vent (D.pulse i) (∏ j∈p,(X (e j):Paper I ℝ))=∑ j∈p,D.pulse i (e j) • ∏ k∈p.erase j,(X (e k):Paper I ℝ):=by
 let g(a:K): Stem I ℝ:= Finsupp.single (e a) 1
 have hx a: MvPolynomial.X (e a)=leaf (g a):=by unfold leaf g; rw [Finsupp.linearCombination_single,one_smul]
 have he(w:I→ℝ)(b:K): sense w (g b)=w (e b):=by unfold sense g; rw [Finsupp.linearCombination_single,one_smul]
 simp_rw [hx,taste_prod, he]
lemma kiss(i:I)(p q:Paper I ℝ): D.avg (D.neg.heat (p*X i)*q)=D.avg (D.neg.heat p * vent (D.pulse i) q) := by
 rw [heat_x,show D.neg.pulse i= - D.pulse i from rfl,vent_neg, ←sub_eq_add_neg,sub_mul,map_sub,mul_assoc, mul_comm (X i),D.release,vent_l,map_add,mul_comm (vent _ (D.neg.heat  _)) q]; abel
variable (A:I→I→ℝ)
def Tops:= ∀ i j, |D.pulse i j| ≤ A i j

lemma withinPay (m:K→I)(s:Finset K) : ∃ C>0, ∀ D:Dose I ℝ, Tops D A→ |D.avg (∏ j∈s,(X (m j):Paper I ℝ))| ≤ C:=by
 induction s using Finset.strongInduction with | H s h =>
   by_cases hx : s.Nonempty
   · obtain ⟨i,hi⟩:=hx
     choose C hc H using (fun j:K=>h ((s.erase i).erase j) (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset hi)))
     let F j:= |A (m i) (m j)| * C j
     refine ⟨(∑ j∈s.erase i,F j)+1,add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun y _=>by unfold F; exact mul_nonneg (abs_nonneg _) (hc y).le)) zero_lt_one,?_⟩ -- fix
     intro D hD;rw [←Finset.prod_erase_mul _ _ hi,D.release,straights,map_sum]
     apply (Finset.abs_sum_le_sum_abs _ _).trans
     apply (Finset.sum_le_sum ?_).trans (show (∑ j∈s.erase i,F j) ≤ _ by linarith)
     intro j hj; rw [map_smul,smul_eq_mul,abs_mul]; exact mul_le_mul ((hD ..).trans (le_abs_self _)) (H j D hD) (abs_nonneg _) (abs_nonneg _)
   rw [Finset.not_nonempty_iff_eq_empty.mp hx,Finset.prod_empty]; refine ⟨2,by norm_num,fun D h'=>?_⟩; rw [avg_one]; norm_num

lemma remotePay (C:I→I→ℝ)(m:K→I)(t:Finset K)(w:B→I)(p:Finset B): ∃ W>0,∀ (D:Dose I ℝ) (n:ℝ), Tops D A → 0≤n → (∀ i∈p,∀ j∈t,|D.pulse (w i) (m j)| * n ≤ C (w i) (m j)) →
   |D.avg (D.neg.heat (∏ i∈p,X (w i))*(∏ j∈t,(X (m j):Paper I ℝ)))| * n^p.card ≤ W:=by
 induction p using Finset.induction_on generalizing t with
 | empty=>
   obtain ⟨W,hW,H⟩:= withinPay A m t; refine ⟨W,hW,fun D n hD hn hΩ=>by simpa only [Finset.prod_empty,heat_one,one_mul, Finset.card_empty,pow_zero,mul_one] using H D hD⟩
 | insert i p hi hp=>
   choose E HE H using fun j => hp (t.erase j)
   let F j:= |C (w i) (m j)| * E j
   refine ⟨(∑ j∈t,F j)+1, add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _=> by unfold F; exact mul_nonneg (abs_nonneg _) (HE j).le) zero_lt_one,?_⟩
   intro D n hD hn hk
   rw [Finset.prod_insert hi,mul_comm (X (w i)) _, kiss,straights, Finset.card_insert_of_notMem hi, Finset.mul_sum,map_sum]
   have G(j) (hj:j∈t):= hk i (Finset.mem_insert_self ..) j hj
   apply le_trans (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (pow_nonneg hn _)); rw [Finset.sum_mul]
   apply (Finset.sum_le_sum ?_).trans (show (∑ j∈t,F j) ≤ _ by linarith)
   intro j hj; rw [pow_succ, mul_smul_comm, map_smul,smul_eq_mul,abs_mul]
   let r:= D.avg (D.neg.heat (∏ b∈p,X (w b))*(∏ k∈t.erase j,X (m k)))
   have he: |r| * n^p.card ≤ E j:= H j D n hD hn (fun a ha v hv=>hk a (Finset.mem_insert_of_mem ha) v (Finset.mem_of_mem_erase hv))
   exact (le_of_eq (show |D.pulse _ _| * |r| * (n^p.card*n)= |D.pulse (w i) (m j)| * n*(|r| * n^p.card) by ring)).trans (mul_le_mul ((G j hj).trans (le_abs_self _)) he (by positivity) (abs_nonneg _))

variable {U V : Type*}(w:U→I)(m:V→I)
lemma remote_body (C:I→I→ℝ)(p:Finset B)(v:B→U)(q:Paper V ℝ): ∃ W>0,∀ (D:Dose I ℝ)(n:ℝ), Tops D A→0≤n→(∀ i j, |D.pulse (w i) (m j)| * n ≤ C (w i) (m j))→
 |D.avg (D.neg.heat (∏ i∈p,X (w (v i))) * rename m q)| * n^p.card ≤ W:=by
 let L(D:Dose I ℝ): Paper V ℝ→ₗ[ℝ] ℝ:= D.avg.comp ((LinearMap.mul ℝ _ (D.neg.heat (∏ i∈p,X (w (v i))))).comp (rename m).toLinearMap)
 change ∃ W>0,∀ (D:Dose I ℝ)(n:ℝ), Tops D A→0≤n→_→|L D q| * n^p.card≤ W
 have he (a:V→₀ℕ)(r:ℝ): ∃ W>0,∀ (D:Dose I ℝ)(n:ℝ), Tops D A→0≤n→(∀ i j,|D.pulse (w i) (m j)| * n≤ C (w i) (m j))→ |L D (monomial a r)| * n^p.card≤ W:=by
   let Y:=(b: ↥a.support)× Fin (a b.val)
   let d:Y→V:=fun i=>i.1.val
   have Hb: (monomial a r)=r • ∏ i:Y, (X (d i):Paper V ℝ):=by
     rw [monomial_eq, C_mul',Finsupp.prod,← Finset.prod_attach]; congr 1; unfold Y d; rw [Fintype.prod_sigma];simp
   obtain ⟨Z,hZ,H⟩:= remotePay A C (m∘d) Finset.univ (w∘v) p
   refine ⟨(|r|+1)*Z,by positivity,?_⟩; intro D n hD hn hm
   rw [Hb,map_smul,smul_eq_mul, abs_mul,mul_assoc]; refine le_trans (b:=|r| * Z) (mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)) (mul_le_mul_of_nonneg_right (by linarith) hZ.le)
   unfold L; simp only [LinearMap.comp_apply,AlgHom.toLinearMap_apply,LinearMap.mul_apply', _root_.map_prod,rename_X]
   exact H D n hD hn (fun _ _ _ _=>hm ..)
 choose X HX H using he
 refine ⟨(∑ a∈q.support,X a (MvPolynomial.coeff a q))+1,add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _=> (HX i _).le) zero_lt_one,?_⟩; intro D n hD hn h
 conv_lhs=> rw [← q.support_sum_monomial_coeff]
 rw [map_sum]; apply le_trans (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (pow_nonneg hn _)); rw [Finset.sum_mul]; refine (Finset.sum_le_sum fun i hi=> H i _ D n hD hn h).trans (show (∑ a∈q.support,X a (coeff a q)) ≤ _ by linarith)

lemma remotePrice {p:Paper U ℝ}{d:ℕ}(hp:IsHomogeneous p d)(C:I→I→ℝ)(q:Paper V ℝ): ∃ W>0,∀ (D:Dose I ℝ)(n:ℝ), Tops D A→0≤n→ (∀ i j,|D.pulse (w i) (m j)| * n≤C (w i) (m j))→
 |D.avg (D.neg.heat (rename w p) * rename m q)| * n^d≤W:=by
 let L (D:Dose I ℝ) : Paper U ℝ→ₗ[ℝ] ℝ:=D.avg.comp ((LinearMap.mulLeft ℝ (rename m q)).comp (D.neg.heat.comp (rename w).toLinearMap))
 have he (a:U→₀ℕ)(r:ℝ) : ∃ W>0,∀ (D:Dose I ℝ)(n:ℝ), Tops D A →0≤n→ (∀ i j,|D.pulse (w i) (m j)| * n≤C (w i) (m j))→ |L D (monomial a r)| * n^(∑ b∈a.support,a b) ≤ W:=by
   let Y:=(b: ↥a.support)× Fin (a b.val); let v:Y→U:=fun i=>i.1.val
   have Hb: (monomial a r)=r • ∏ i:Y, (X (v i):Paper U ℝ):=by
     rw [monomial_eq, C_mul',Finsupp.prod, ← Finset.prod_attach]; congr 1; unfold Y v; rw [Fintype.prod_sigma]; simp
   obtain ⟨Z,hZ,H⟩:=remote_body A w m C Finset.univ v q
   refine ⟨(|r|+1)*Z,by positivity,?_⟩; intro D n hD hn h
   rw [Hb,map_smul,smul_eq_mul,abs_mul,mul_assoc]
   refine le_trans (b:=|r| * Z) (mul_le_mul_of_nonneg_left ?_ (abs_nonneg r)) (mul_le_mul_of_nonneg_right (by linarith) hZ.le)
   unfold L; simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod,rename_X]
   rw [show (∑ b∈a.support,a b) = Finset.univ.card (α:=Y) from by simp [Y, Fintype.card_sigma]; exact (Finset.sum_attach a.support (a : U→ℕ)).symm]
   specialize H D n hD hn h; rw [mul_comm (D.neg.heat _)] at H; exact H
 choose x hx H using he
 refine ⟨(∑ a∈p.support,x a (coeff a p))+1,add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _=> (hx i _).le) zero_lt_one,?_⟩; intro D n hD hn hk
 rw [mul_comm (D.neg.heat _)]; change |L D p| * n^d≤_
 conv_lhs=> rw [← p.support_sum_monomial_coeff]
 rw [map_sum]; apply le_trans (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (pow_nonneg hn _)); rw [Finset.sum_mul]; refine (Finset.sum_le_sum fun i hi=>?_).trans (show (∑ a∈p.support,x a (coeff a p)) ≤ _ by linarith)
 rw [hp.degree_eq_sum_deg_support hi]; exact H _ _ D n hD hn hk
end YM.SchemeRG11.Haze
