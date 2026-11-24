import YM.WilsonCoeffUV.Test.Derivatives
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! y^ν/ν! tests on Chamber. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Embroider
open Filter Function Set Lattice RG Analysis
open scoped Topology BigOperators ContDiff
variable {D d h:ℕ}
def twists (u:Fin d→Axis):Multiset Axis:=(List.ofFn u : Multiset Axis)
@[simp] lemma twists_card (u:Fin d→Axis): (twists u).card=d:=by simp [twists]
lemma twists_cons (u:Fin d→Axis)(i:Axis): twists (Fin.cons i u)= i::ₘtwists u:=by simp [twists]
lemma twist_disorder (p q:Fin d→Axis)(h:twists p=twists q): ∃ σ:Equiv.Perm (Fin d),p=q ∘ σ:=by
    have hc : List.Perm (List.ofFn p) (List.ofFn q):= Multiset.coe_eq_coe.mp h
    let a:= Tuple.sort p; let b:= Tuple.sort q
    have he: p ∘ a=q ∘ b:= List.ofFn_injective ((a.ofFn_comp_perm p |>.trans (hc.trans (b.ofFn_comp_perm q).symm)).eq_of_pairwise' (Tuple.monotone_sort _).sortedLE_ofFn.pairwise (Tuple.monotone_sort _).sortedLE_ofFn.pairwise)
    refine ⟨a.symm.trans b,funext fun i=>?_⟩
    simpa using congr_fun he (a.symm i)
lemma creased_for_twist (p q:Fin d→Axis)(h:twists p=twists q)(f:Scroll D)(hp:d≤ D)(x:E): crease f p x=crease f q x:=by
    obtain ⟨s,rfl⟩:=twist_disorder p q h; exact sym_Jet (scribble f hp).contDiffAt (dot ∘ q) s

abbrev Spiral (h:ℕ):= {k:Multiset Axis // k.card ≤ h}
def rankS (i:Spiral h):ℕ:= i.val.card
lemma present (i:Multiset Axis) :∃ u:Fin i.card→Axis,twists u=i:=by
   induction i using Multiset.induction_on with
   | empty => exact ⟨fun _=>0,rfl⟩
   | @cons i s ih =>
      obtain ⟨u,hu⟩:=ih
      suffices H : ∀ (m:ℕ)(h:m=s.card+1),∃ u:Fin m→Axis,twists u=i::ₘs by exact H _ (Multiset.card_cons ..)
      rintro _ rfl; exact ⟨Fin.cons i u,by rw [twists_cons,hu]⟩
instance :Fintype (Spiral h) :=
    let u:Knob h → Spiral h := fun i=>⟨twists i.2,by rw [twists_card]; exact Nat.le_of_lt_succ i.1.isLt⟩
    Fintype.ofSurjective u (fun i=> by
       obtain ⟨v,hv⟩:=present i.val; exact ⟨⟨⟨rankS i, Nat.lt_succ_of_le i.property⟩,v⟩,Subtype.ext hv⟩)

def knurl (i:Spiral h): Fin (rankS i)→Axis:= (present i.val).choose
lemma knurls (i:Spiral h): twists (knurl i)=i.val:= (present _).choose_spec

private def ma (s:Multiset Axis)(i:Axis)(x:E):= x i^(s.count i)*((s.count i).factorial:ℝ)⁻¹
def mica (s:Multiset Axis)(x:E):ℝ:= ∏ i:Axis, ma s i x
lemma mica_smooth (s:Multiset Axis)(n:WithTop ℕ∞): ContDiff ℝ n (mica s):=by unfold mica ma; fun_prop
private lemma mint (s:Multiset Axis)(i:Axis)(x:E): Analysis.D (dot i) (mica s) x=
      (if i∈s then mica (s.erase i) x else 0):=by
   let A j : E→L[ℝ]ℝ:= ContinuousLinearMap.proj j
   have he (j:Axis): fderiv ℝ (ma s j) x (dot i)=(s.count j:ℝ)*x j^(s.count j-1)*dot i j*((s.count j).factorial:ℝ)⁻¹:=by
       change fderiv ℝ ((A j: E→ ℝ)^ (s.count j) * (fun _ : E=> ((s.count j).factorial:ℝ)⁻¹)) x (dot i)= _
       rw [fderiv_mul ((A j).differentiableAt.pow _) (differentiableAt_const _), fderiv_pow _ (A j).differentiableAt,ContinuousLinearMap.fderiv]; simp [A]; ring
   rw [Analysis.D]; change fderiv _ (fun x => ∏ j, ma s j x) x (dot i)= _; rw [fderiv_finsetProd (g:=ma s) (fun i _=> by unfold ma; fun_prop), sum_apply, Finset.sum_eq_single i]
   · rw [smul_apply,he, show dot i i=1 from Pi.single_eq_same i 1,mul_one, smul_eq_mul]
     by_cases h:i∈s
     · rw [if_pos h, mica,← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
       congr 1
       · apply Finset.prod_congr rfl; intro j hj; rw [ma,ma,Multiset.count_erase_of_ne (Finset.mem_erase.mp hj).1]
       rw [ma, Multiset.count_erase_self]
       have hq:= Multiset.count_pos.mpr h; cases g:s.count i with
       | zero=> omega
       | succ n=> simp [Nat.factorial_succ]; ring_nf; field_simp; ring
     rw [if_neg h,Multiset.count_eq_zero.mpr h]; simp
   · intro j hj hi; rw [smul_apply,he,show dot i j=0 from Pi.single_eq_of_ne hi _]; simp
   simp

def testa (D)(s:Multiset Axis): Scroll D:=⟨mica s,mica_smooth s (↑D)⟩
private lemma nopeat (i:Axis)(p:Fin d→Axis): dot ∘ Fin.cons i p=Fin.cons (dot i) (dot ∘ p):= funext fun j=>Fin.cases rfl (fun _=>rfl) j
private lemma frost (p:Multiset Axis):mica p 0 = (if p=0 then 1 else 0):=by
   by_cases he:p=0
   · rw [if_pos he,he]; simp [mica,ma]
   obtain ⟨i,hi⟩:= Multiset.exists_mem_of_ne_zero he
   rw [if_neg he,mica]; exact Finset.prod_eq_zero (Finset.mem_univ i) (by unfold ma; simp [(Multiset.count_pos.mpr hi).ne'])
lemma coinage (D) (p:Multiset Axis)(v:Fin d→Axis): crease (testa D p) v 0=if p=twists v then 1 else 0:=by
   induction d generalizing p with
   | zero=> change iteratedFDeriv ℝ 0 (mica p) 0 _= _; simp_rw [iteratedFDeriv_zero_apply]; exact frost p
   | succ d ih =>
       obtain ⟨i,v,rfl⟩ :∃ i v', v=Fin.cons i v':=⟨_,_,(Fin.cons_self_tail v).symm⟩
       change iteratedFDeriv ℝ (d+1) (mica p) 0 _= _
       rw [nopeat, cons_inner (mica_smooth _ _).contDiffAt,twists_cons]
       by_cases h:i∈p
       · rw [show Analysis.D (dot i) (mica p)=mica (p.erase i) from funext fun _=>by rw [mint,if_pos h], show iteratedFDeriv ℝ d (mica (p.erase i)) 0 (dot ∘ v) = (if p.erase i = twists v then 1 else 0) from ih ..]; simp only [show p.erase i= twists v ↔ p= i::ₘtwists v from ⟨fun a=>by rw [←a]; simp [h],fun b=>by rw [b]; simp ⟩]
       rw [show Analysis.D (dot i) (mica p)= (fun _=>0) from funext fun _=>by rw [mint,if_neg h], if_neg (fun g=> h (by rw [g]; simp))]; simp
lemma coins_empty (p:Multiset Axis)(v:Fin d→Axis)(he:p.card<d)(x:E): crease (testa D p) v x=0:=by
   induction d generalizing p with
   | zero => omega
   | succ d ih =>
       obtain ⟨i,v,rfl⟩ :∃ i v',v=Fin.cons i v':=⟨_,_,(Fin.cons_self_tail v).symm⟩
       change iteratedFDeriv ℝ (d+1) (mica p) x _= _
       rw [nopeat,cons_inner (mica_smooth _ _).contDiffAt]
       by_cases h:i∈p
       · rw [show Analysis.D (dot i) (mica p)=mica (p.erase i) from funext fun _=>by rw [mint,if_pos h]]
         exact ih _ _ (by rw [Multiset.card_erase_of_mem h]; have := Multiset.card_pos.mpr (show p≠0 from fun hx=>by rw [hx] at h; simp at h); rw [Nat.pred_eq_sub_one]; omega)
       rw [show Analysis.D (dot i) (mica p)= (fun _=>0) from funext fun _=>by rw [mint,if_neg h]]; simp
end YM.WilsonCoeffUV.Embroider
