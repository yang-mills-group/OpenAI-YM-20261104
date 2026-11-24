import YM.RegulatorIR.Diagram.Laplace
import YM.RegulatorIR.Diagram.Valence

/-! Rank sums for each of the two recursions. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Diagram
open Finset MvPolynomial Function Budget Budget.Packet
open scoped Topology BigOperators Classical
variable {I : Type}{m n r:ℕ}[Fintype I]

def packed (T:Ranked I)(n:ℕ): Jet I:=∑ i∈Finset.range (n+1), render (T i)
lemma pack_extends {T:Ranked I}(h:Within n T) (hk:n≤m) : packed T n=packed T m := by
 apply Finset.sum_subset (show range (n+1)⊆range (m+1) from range_mono (by omega))
 intro x _ he; rw [show T x=0 from by by_contra! h'; apply he; exact mem_range.mpr (Nat.lt_succ_of_le (h _ h')),render_zero]
lemma pack_add (T U:Ranked I)(n:ℕ):packed (T+U) n=packed T n+packed U n:=by simp_rw [packed,Pi.add_apply,render_add,Finset.sum_add_distrib]
lemma pack_smul (T:Ranked I)(x:ℝ)(n:ℕ):packed (x • T) n=C x * packed T n:=by simp only [packed,Pi.smul_apply,render_scale,Finset.mul_sum]
lemma pack_sum {X : Type}(s : Finset X)(T:X→Ranked I)(n:ℕ) : packed (∑ i∈s,T i) n =∑ i∈s,packed (T i) n :=by
 simp_rw [packed,Finset.sum_apply,render_sum];rw [Finset.sum_comm]
lemma pack_multiplicity {T:Ranked I}(K:Layer I I)(h:Within n T)(hh:∀ i,IsSym (T i)): packed (heating K T) n=C (2:ℝ)⁻¹ * sweep K (packed T n):=by
 rw [pack_extends h (show n≤n+2 by omega)]
 unfold packed; rw [sweep_sum K ..]
 rw [Finset.sum_range_succ' (n:=n+2), sweep_const,add_zero,Finset.sum_range_succ' (n:=n+1),sweep_linear,add_zero, Finset.mul_sum]
 apply Finset.sum_congr rfl;intro i hi
 rw [render_loop K (T _) (hh _),heating,render_scale,render_symmetry];rw [div_eq_mul_inv]; simp only [map_mul,map_add,map_natCast,map_ofNat,map_one]; ring

lemma matchRender (K:Layer I I)(T S:Ranked I)(p q :ℕ)(h:IsSym (T (p+1)))(hh:IsSym (S (q+1))):
    render (matchTwo K T S (p+q) (p,q))=meet K (render (T (p+1))) (render (S (q+1))):=by
 rw [render_join K _ _ h hh,matchTwo,dif_pos rfl];change render ((_ : ℝ) • symmetry _) = _
 rw [render_scale,render_symmetry]; simp
lemma meet_many {α β:Type} (p : Finset α)(q:Finset β)(T:α→Jet I)(S:β→Jet I)(K:Layer I I):
     meet K (∑ i∈p,T i) (∑ j∈q,S j)=∑ i∈p,∑ j∈q,meet K (T i) (S j) :=by
 unfold meet; simp only [map_sum,mul_sum,sum_mul]
 -- nested sum permutation
 rw [Finset.sum_comm (s:=p) (t:=q)]
 -- simp commute univ Φ binders (distinguish arbitrary p t)
 simp_rw [Finset.sum_comm (s:=@Finset.univ I _) (t:=q)]
 simp_rw [Finset.sum_comm (s:=@Finset.univ I _) (t:=p)]
lemma pack_force (K:Layer I I)(T S:Ranked I)(h:Within (n+1) T)(he:Within (m+1) S) (hx:∀ i,IsSym (T i))(hy:∀ i,IsSym (S i)) :
      packed (force K T S) (n+m) = meet K (packed T (n+1)) (packed S (m+1)) := by
 let f (p:ℕ×ℕ):= meet K (render (T (p.1+1))) (render (S (p.2+1)))
 have ha : packed (force K T S) (n+m) = ∑ i∈range (n+m+1), ∑ j∈Finset.antidiagonal i,f j:= by
    unfold packed force
    apply Finset.sum_congr rfl;intro a _;rw [render_sum]; apply Finset.sum_congr rfl; rintro ⟨i,j⟩ hv
    rw [← Finset.mem_antidiagonal.mp hv]; exact matchRender K T S i j (hx _) (hy _)
 have hh : meet K (packed T (n+1)) (packed S (m+1))=∑ i∈ range (n+1) ×ˢ range (m+1),f i:= by
    unfold packed; rw [meet_many,Finset.sum_range_succ' (n:=n+1)];
    have ho (k:ℕ): meet K (render (T 0)) (render (S k))=0:=by unfold meet;simp [pderiv_scale_zero]
    have ho' (k:ℕ) : meet K (render (T k)) (render (S 0))=0 := by unfold meet; simp [pderiv_scale_zero]
    rw [Finset.sum_product]; simp_rw [ho]; rw [Finset.sum_const_zero,add_zero]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_range_succ',ho', add_zero]
 rw [ha,hh,← Finset.sum_biUnion]
 · symm; apply Finset.sum_subset
   · rintro ⟨i,j⟩ ht
     obtain ⟨u,v⟩:=Finset.mem_product.mp ht
     simp only [mem_range] at u v
     exact Finset.mem_biUnion.mpr ⟨i+j,mem_range.mpr (by omega), Finset.mem_antidiagonal.mpr rfl⟩
   rintro ⟨i,j⟩ _ ht
   by_cases hi:i∈range (n+1)
   · rw [show f (i,j)=meet _ _ (render (S (j+1))) from rfl,show S (j+1)=0 from ?_]; simp [meet]
     by_contra! hv; exact ht (mem_product.mpr ⟨hi,mem_range.mpr (show j<m+1 from by have := he (j+1) hv; omega)⟩)
   rw [show f (i,j)=meet _ (render (T (i+1))) _ from rfl,show T (i+1)=0 from ?_]; simp [meet]
   by_contra! hv; exact hi (mem_range.mpr (by have := h (i+1) hv; omega))
 intro i _ j _ ht; exact Finset.disjoint_left.mpr (fun a ha hb=> ht ((Finset.mem_antidiagonal.mp ha).symm.trans (Finset.mem_antidiagonal.mp hb)))
end YM.RegulatorIR.Diagram
