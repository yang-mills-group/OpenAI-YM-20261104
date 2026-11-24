import YM.WilsonCoeffUV.Product.Connected.Derive
import YM.WilsonCoeffUV.Marked.Step.Horizon
/-!
# Square-free-marker cumulant algebra
At fixed positions (no permutation or RG gauge tags yet). Representatives or
auxiliaries killing further configurations preserve entries on *allowed*
sets---all inputs over subsets. Re-express Planck outputs thus on slots.
This Euler convention avoids factorial complications. `Pleaf ⋆ M` means
usual subset convolution with repeated slot marks killed. Formal derivative
with respect to monomial dilation is literally `card S • v S`.
The unit is included, and log relation is `exp(cumulants)=ordinary`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function MvPolynomial Blue
open scoped BigOperators
variable {ι:Type}{R:Type}{J K S T: Finset ι}
section alg
variable [DecidableEq ι] [CommRing R]
abbrev Sac (ι R: Type):= Finset ι→R

def shells (M L:Sac ι R) (S: Finset ι): R:= ∑ J∈S.powerset,M J*L (S\J)
lemma shells_emp (M L:Sac ι R): shells M L ∅=M ∅*L ∅:=by simp [shells]
lemma shells_l (M L A: Sac ι R): shells (M+L) A= shells M A+shells L A:=by funext s; simp [shells,add_mul,Finset.sum_add_distrib]
lemma shells_m (M L A: Sac ι R): shells (M-L) A= shells M A-shells L A:=by funext s; simp [shells,sub_mul,Finset.sum_sub_distrib]
lemma shells_g (B:Finset ι→Sac ι R)(M:Sac ι R)(S: Finset (Finset ι)): shells (∑ i∈S,B i) M= ∑ i∈ S,shells (B i) M:=by funext n; simp_rw [shells,Finset.sum_apply,Finset.sum_mul]; rw [Finset.sum_comm]; rfl
lemma twin_l (h:J⊆S): S\(S\J)=J:=by ext i; simp; grind
lemma shores (L M:Sac ι R): shells L M=shells M L:=by
   funext n; apply Finset.sum_bij (fun i _=> n\i)
   · exact fun i _=> Finset.mem_powerset.mpr Finset.sdiff_subset
   · intro i hi j hj e; rw [←twin_l (Finset.mem_powerset.mp hi),e,twin_l (Finset.mem_powerset.mp hj)]
   · exact fun i hi=>⟨_,Finset.mem_powerset.mpr Finset.sdiff_subset,twin_l (Finset.mem_powerset.mp hi)⟩
   intro i hi; rw [twin_l (Finset.mem_powerset.mp hi),mul_comm]
lemma littoral (L M O:Sac ι R): shells (shells L M) O=shells L (shells M O):=by
    funext S; unfold shells; simp_rw [Finset.sum_mul,Finset.mul_sum]; rw [Finset.sum_sigma', Finset.sum_sigma']
    -- map from nested inclusion K⊆ J⊆ S to K and H⊆S\K via J\K
    refine Finset.sum_bij (fun v _=>Sigma.mk (β:=fun _:Finset ι=>Finset ι) v.2 (v.1\v.2)) ?_ ?_ ?_ ?_
    · simp only [Finset.mem_sigma,Finset.mem_powerset]; intro a h; exact ⟨h.2.trans h.1,by intro i hi; exact Finset.mem_sdiff.mpr ⟨h.1 (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩⟩
    · rintro ⟨a,b⟩ ha ⟨c,d⟩ hc he; simp only [Finset.mem_sigma,Finset.mem_powerset] at ha hc; simp at he
      obtain ⟨rfl,H⟩:= he; have ht: a=c:=by
          ext x; have h : x∈a\b ↔ x∈c\b:=by rw [H]
          grind
      subst c; rfl
    · rintro ⟨i,j⟩ hj; simp only [Finset.mem_sigma,Finset.mem_powerset] at hj
      refine ⟨⟨i∪j,i⟩,Finset.mem_sigma.mpr ⟨Finset.mem_powerset.mpr (Finset.union_subset hj.1 (hj.2.trans Finset.sdiff_subset)),Finset.mem_powerset.mpr Finset.subset_union_left⟩,?_⟩; apply congr_arg (Sigma.mk i); ext; grind
    · rintro ⟨i,j⟩ hi; simp only [Finset.mem_sigma,Finset.mem_powerset] at hi; dsimp only
      rw [mul_assoc]; have h:(S\j)\(i\j)= S\i:=by ext; grind;
      rw [h]

def dial (L:Sac ι R)(S:Finset ι):R:= S.card • L S
omit [DecidableEq ι] in
lemma dial_p (L M: Sac ι R): dial (L+M)=dial L+dial M:=funext fun _=> nsmul_add ..
omit [DecidableEq ι] in
lemma dial_d (L M: Sac ι R): dial (L-M)=dial L-dial M:=funext fun _=> smul_sub ..
lemma dial_shell (L M:Sac ι R): dial (shells L M) = shells (dial L) M + shells L (dial M):=by
    funext S; simp only [dial,shells,Pi.add_apply, nsmul_eq_mul,Finset.mul_sum, ←Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro J hJ; have h : (S\J).card + J.card = S.card:=Finset.card_sdiff_add_card_eq_card (Finset.mem_powerset.mp hJ); simp only [←h,Nat.cast_add]; ring

def Equation (M L:Sac ι R):Prop:= M ∅=1 ∧ L ∅=0 ∧ dial M=shells (dial L) M
lemma shells_cancel (M A B: Sac ι R)(h: M ∅=1)(e:shells A M=shells B M): A=B:=by
    let P:=A-B
    have he:shells P M=0:=by rw [show P=_ from rfl,shells_m,e,sub_self]
    apply sub_eq_zero.mp
    funext i; induction i using Finset.strongInduction with
    | H k ih=>
       have hx:=congr_fun he k; rw [shells,Finset.sum_eq_single k,Finset.sdiff_self,h,mul_one] at hx; exact hx
       · intro i hi HV; rw [show P i=0 from ih _ (lt_of_le_of_ne (Finset.mem_powerset.mp hi) HV),zero_mul]
       simp

variable [IsAddTorsionFree R]
lemma Equation.unique (M L V: Sac ι R)(h:Equation M L)(p:Equation M V): L=V:=by
    have hx:= shells_cancel M (dial L) (dial V) h.1 (h.2.2.symm.trans p.2.2)
    funext S; by_cases hz:S=∅; · subst S; rw [h.2.1, p.2.1]
    exact (smul_right_inj (M:=R) (by simpa using hz : S.card ≠ 0)).mp (congr_fun hx S)
lemma dial_null (L A:Sac ι R)(h:A ∅=0)(e:dial A=shells (dial L) A): A=0:=by
    funext i; induction i using Finset.strongInduction with
    | H k ih=>
       by_cases ht:k=∅; · subst k; exact h
       have he:k.card • A k = k.card • (0: R):=by
          rw [smul_zero,show k.card • A k=dial A k from rfl,e]; apply Finset.sum_eq_zero; intro j hp; by_cases H:j=∅; · simp [H,dial]
          have hv:=Finset.mem_powerset.mp hp
          have hs:(k\j)⊂k:=by refine lt_of_le_of_ne Finset.sdiff_subset ?_; intro q; have h:=twin_l hv; rw [q,Finset.sdiff_self] at h; exact H h.symm
          rw [show A (k\j)=0 from ih _ hs,mul_zero]
       exact (smul_right_inj (M:=R) (by simpa using ht : k.card ≠ 0)).mp he
lemma Equation.prod_u (M L V:Sac ι R)(h:Equation M L)(p:Equation V L): M=V:=by
   apply sub_eq_zero.mp; refine dial_null L (M-V) ?_ ?_; · rw [Pi.sub_apply,p.1,h.1, sub_self]
   rw [dial_d,h.2.2,p.2.2,shores (dial L) (M-V),shells_m,shores M (dial L),shores V (dial L)]

section Tint
variable [Algebra ℝ R]
omit [IsAddTorsionFree R] in
lemma scan_map (A:Derivation ℝ R R)(L M: Sac ι R): A ∘ shells L M=shells (A ∘ L) M+shells L (A ∘ M):= by
    funext n; simp only [comp_apply, Pi.add_apply,shells, map_sum,Derivation.leibniz,Finset.sum_add_distrib]; rw [add_comm]; congr 1; apply Finset.sum_congr rfl; intro i _; rw [smul_eq_mul,mul_comm]

lemma Equation.track (M L: Sac ι R)(h: Equation M L)(A:Derivation ℝ R R): A ∘ M=shells (A ∘ L) M:=by
   have e:dial (A ∘ M)=dial (shells (A ∘ L) M)+shells (dial L) (A ∘ M-shells (A ∘ L) M):=by
       have he (v : Sac ι R) : dial (⇑A ∘ v) = (⇑A ∘ dial v):=funext fun n=>Eq.symm (map_nsmul A n.card (v n))
       rw [he M,h.2.2, scan_map,dial_shell,he L]
       rw [shores (dial L) (_-_),shells_m,shores (A ∘ M),h.2.2, littoral (⇑A ∘ L)]
       rw [shores M (dial L)]
       abel
   apply sub_eq_zero.mp; apply dial_null L _; · simp [Pi.sub_apply, shells_emp,h.1,h.2.1]
   rw [dial_d,e,add_sub_cancel_left]
end Tint
end alg
end YM.WilsonCoeffUV.Wheel.Mark
