import YM.RG11Proof.Rigidity.Reads.Words

/-!
# Words in the Maxwell quotient, converse existence
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Reads
open Maxwell Maxwell.Free Crowd Prism Function Submodule
open scoped BigOperators Classical
variable {G:Gauge}

lemma canon_append (a b:Cast G):canon (a++b)=canon a+canon b:=by simp [canon,List.sum_append]
private def tintC (s : ℝ)(p : Cast G): Cast G:= p.map (fun i=>(s*i.1,i.2))
lemma canon_scale (p : Cast G)(s:ℝ): canon (tintC s p)=(s:ℂ) • canon p:=by
  induction p with
  | nil=>simp [tintC,canon]
  | cons a l ih=>
    change (↑(s*a.1):ℂ) • emits a.2+canon (tintC s l) = (s:ℂ) • (_+canon l)
    rw [smul_add,ih, Complex.ofReal_mul,mul_smul]

def stalls (G:Gauge) : Submodule ℝ (WickPol G) where
  carrier := Set.range canon
  zero_mem' := ⟨[],rfl⟩
  add_mem' ha hb:=by rcases ha with ⟨p,rfl⟩; rcases hb with ⟨q,rfl⟩; exact ⟨_,canon_append p q⟩
  smul_mem' t _ ha:= by rcases ha with ⟨p,rfl⟩; exact ⟨_,(canon_scale p t).trans ((RCLike.real_smul_eq_coe_smul (K:=ℂ) t _).symm)⟩

lemma stalls_atom (p : Article G): emits p ∈ stalls G:= show emits p ∈ Set.range canon from ⟨[(1,p)], by simp [canon]⟩
lemma stalls_prod {a b : WickPol G} (h : a∈ stalls G) (ht : b∈stalls G): a*b∈stalls G:=by
  obtain ⟨p,rfl⟩:= (h:Set.range canon a); obtain ⟨q,rfl⟩:= (ht:Set.range canon b)
  induction p with
  | nil=>simp [canon]
  | cons i l ih=>
    change ((_ • _) + canon l)*_ ∈ _; rw [add_mul]; refine Submodule.add_mem _ ?_ ih
    clear ih; induction q with
    | nil=>simp [canon]
    | cons j P h=>
      change _*(((j.1:ℂ) • emits j.2)+canon P)∈_
      rw [mul_add]; refine Submodule.add_mem _ ?_ h
      rw [smul_mul_assoc,mul_smul_comm,smul_smul,← Complex.ofReal_mul]
      rw [show (↑(i.1*j.1):ℂ) • (emits i.2*emits j.2)=(i.1*j.1) • _ from (RCLike.real_smul_eq_coe_smul (K:=ℂ) (i.1*j.1) _).symm]
      apply Submodule.smul_mem; rw [show emits i.2*emits j.2=emits (i.2++j.2) by simp [emits,List.prod_append]]; exact stalls_atom _

lemma letter_admitted {j} (p : Probe G j): symbol j p∈ stalls G:=by
  rw [divide]; apply Submodule.sum_mem; intro c _; simpa only [emits,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,Dart.write,Dart.flip,Free.letter,bit] using stalls_atom (G:=G) [⟨j,c,flavor_pick p c⟩]

lemma mixes (p : WickPol G): ∃ a∈ stalls G,∃ b∈ stalls G,p=a + Complex.I • b := by
  induction p using MvPolynomial.induction_on with
  | C c=>
    refine ⟨c.re • emits [], (stalls G).smul_mem _ (stalls_atom []),c.im • emits [],(stalls G).smul_mem _ (stalls_atom []),?_⟩
    change MvPolynomial.C c=c.re • (1: WickPol G)+ Complex.I • c.im • (1: WickPol G)
    rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) c.re,RCLike.real_smul_eq_coe_smul (K:=ℂ) c.im,smul_smul,← add_smul,mul_comm (Complex.I)]; change MvPolynomial.C c=((c.re:ℂ)+(c.im:ℂ)*Complex.I) • (1: WickPol G); rw [show ((c.re:ℂ)+(c.im:ℂ)*Complex.I)=c from Complex.re_add_im c,← MvPolynomial.C_mul',mul_one]
  | add p q hp hq=>
    obtain ⟨a,ha,b,hb,h⟩:=hp; obtain ⟨i,hi,j,hj,hq⟩:=hq
    rw [h,hq]; exact ⟨_, (stalls G).add_mem ha hi,_, (stalls G).add_mem hb hj,by rw [smul_add];abel⟩
  | mul_X p i hp=>
    obtain ⟨a,ha,b,hb,h⟩:=hp
    rw [h,← symbol_coordinate]; exact ⟨_,stalls_prod ha (letter_admitted (coordinateLeg i)), _,stalls_prod hb (letter_admitted (coordinateLeg i)),by rw [add_mul,smul_mul_assoc]⟩

private theorem stalls_real {p : WickPol G}(h : p∈ stalls G): realForm p=p := by obtain ⟨q,rfl⟩:= (h:Set.range canon p); exact canon_real q
theorem real_spoken {p : WickPol G}(h : realForm p=p): ∃ q,canon q=p := by
  obtain ⟨a,ha,b,hb,hp⟩:=mixes p; rw [hp,map_add,star_smul,stalls_real ha,stalls_real hb,add_right_inj] at h
  have hq : b=0:= by
    simp_rw [Complex.star_def,Complex.conj_I,neg_smul] at h
    exact (smul_eq_zero.mp (show (Complex.I*2) • b=0 by
      rw [mul_comm,mul_smul,two_smul,← sub_neg_eq_add,h,sub_self])).resolve_left (by simp)
  rw [hp,hq,smul_zero,add_zero]; exact ha

/-- Deadline projection can now be performed just on the list of terms. -/
def horn (n : ℕ)(q : Cast G) : Cast G:= q.filter (fun i=> ceilingG i.2==n)
lemma horns (n : ℕ)(q : Cast G) : canon (horn n q)=printed q n := by
  induction q with
  | nil=>rfl
  | cons a l ih=>
    by_cases he : ceilingG a.2=n
    · rw [horn,List.filter_cons_of_pos (by simpa)]; change _ + canon (horn n l) = _+_; simp only [ih,if_pos he]; rfl
    rw [horn,List.filter_cons_of_neg (by simpa)]; change canon (horn n l)=(if _ then _ else 0)+_; rw [ih,if_neg he,zero_add]; rfl

-- Just homogeneous first-track. Recombine after using the adapted filtration
-- preserving coordinate theorem.
theorem hom_present (i : ℕ){p : WickPol G} (h : realForm p=p) (H : MvPolynomial.IsWeightedHomogeneous scaleW p i):
    ∃ q, canon q=p ∧ ∀ a ∈ q,ceilingG a.2=i := by
  obtain ⟨q,rfl⟩:=real_spoken h
  refine ⟨horn i q,?_ ,fun a ha=>of_decide_eq_true ?_⟩ -- use Bool BEq
  · rw [horns,← prints]; exact MvPolynomial.weightedHomogeneousComponent_eq_self H
  · simpa using (List.mem_filter.mp ha).2
end YM.RG11.Rigidity.Reads
