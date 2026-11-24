import YM.Next.MAXWELL.Covariance
import YM.Next.RANK.GaussLeg

/-!
# Transport bounds through the algebraic Gaussian
No positivity or covariance lower bound; arbitrary order polys
in arbitrary slot space. Useful at Gaussian order, also for graphs
with contact subtractions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar
open Set Filter LinearMap Finset Asymptotics
open Next.Rank.Normal
open scoped Classical BigOperators Topology

variable {A V : Type*} {L : Filter A} {R : A → ℝ} {u w p q : A → ℂ}

/-- Perturbation algebra of bounded quantities along the filter. -/
structure Accords (L : Filter A) (R : A → ℝ) (u w : A→ℂ) : Prop where
  bounded : u =O[L] fun _=> (1:ℝ)
  bounded' : w =O[L] fun _=> (1:ℝ)
  differs : (fun x => u x-w x) =O[L] R
namespace Accords

lemma close (h : (fun x => u x-w x)=O[L] R) (H : w =O[L] fun _=> (1:ℝ)) (B : R =O[L] fun _=> (1:ℝ)) : Accords L R u w :=
  ⟨(by simpa using (((h.trans B).add H))), H, h⟩

lemma constants (c:ℂ) : Accords L R (fun _=>c) (fun _=>c) :=
  ⟨isBigO_const_const c one_ne_zero L,isBigO_const_const c one_ne_zero L,by simpa only [sub_self] using isBigO_zero R (E':=ℂ) L⟩

lemma add (h : Accords L R u w) (H : Accords L R p q) : Accords L R (fun x=> u x+p x) (fun x=> w x+q x) :=
  ⟨h.bounded.add H.bounded,h.bounded'.add H.bounded',by simpa only [add_sub_add_comm (u _) (p _)] using (h.differs.add H.differs)⟩
lemma mul (h : Accords L R u w) (H : Accords L R p q) : Accords L R (fun x=> u x*p x) (fun x=> w x*q x) := by
  obtain ⟨U,W,D⟩:=h; obtain ⟨P,Q,E⟩:=H
  refine ⟨by simpa using U.mul P,by simpa using W.mul Q,?_⟩
  rw [show (fun x=> u x * p x-w x*q x)=(fun x=> (u x-w x)*p x+w x*(p x-q x)) from funext (fun x=> by ring)]
  exact (show (fun x=> (u x-w x)*p x)=O[L] R from by simpa using D.mul P).add (by simpa using W.mul E)

lemma sum {Z : Type*} (s : Finset Z) (u v : Z → A→ℂ) (h : ∀ i∈s, Accords L R (u i) (v i)) : Accords L R (fun x=>∑ i∈s,u i x) (fun x=>∑ i∈s,v i x) :=
  ⟨IsBigO.sum fun i hi=> (h i hi).bounded,IsBigO.sum fun i hi=> (h i hi).bounded',by simp_rw [←Finset.sum_sub_distrib]; apply IsBigO.sum; exact fun i hi=>(h i hi).differs⟩

section
variable {Q P : A → Symmetric V} {f g : A→ V →ℂ} (hC : ∀ a b, Accords L R (fun x=>(Q x).cov a b) (fun x=>(P x).cov a b))
variable (hc : ∀ a, Accords L R (fun x=>f x a) (fun x=>g x a))
include hC hc

-- valid before or after contracting external probe legs.
private theorem glyph {I : Type*} (Z : I → V) (s : Finset I) : Accords L R (fun x=> blend (Q x) (f x) (glyphs Z s)) (fun x=>blend (P x) (g x) (glyphs Z s)) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    rcases s.eq_empty_or_nonempty with h|⟨i,hi⟩
    · subst s; simpa only [glyphs,Finset.prod_empty,fresh] using (constants 1 (L:=L) (R:=R))
    have hr:s.erase i ⊂ s:=Finset.erase_ssubset hi
    rw [← insert_erase hi]; simp_rw [spring _ _ _ _ (notMem_erase i s)]
    exact add ((hc (Z i)).mul (ih _ hr)) (sum _ _ _ fun a _=> (hC (Z i) (Z a)).mul (ih _ (Finset.ssubset_of_subset_of_ssubset (erase_subset a _) hr)))

theorem blends (p : poly V) : Accords L R (fun x=> blend (Q x) (f x) p) (fun x=> blend (P x) (g x) p) := by
  let B := MvPolynomial.basisMonomials V ℂ
  have H i : Accords L R (fun x=> blend (Q x) (f x) (B i)) (fun x=> blend (P x) (g x) (B i)):= by
    obtain ⟨v,hv,r⟩:= Maxwell.Free.mon_list i
    rw [show B i=glyphs v.get univ from ?_]
    · exact glyph hC hc _ _
    rw [glyphs, ← List.prod_ofFn]; exact hv.trans (congr_arg List.prod (calc
      _ = (List.ofFn v.get).map _ := by rw [List.ofFn_get]
      _ = _ := List.map_ofFn))
  let y:= B.repr p
  rw [show p=(∑ i∈y.support,y i • B i) from (B.linearCombination_repr p).symm]; simp_rw [_root_.map_sum,map_smul,smul_eq_mul]
  exact sum _ _ _ (fun i _=> (constants (y i)).mul (H i))
end
end Accords
end YM.MSbar
