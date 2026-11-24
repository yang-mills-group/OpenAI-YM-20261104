import YM.WilsonCoeffUV.Marked.Step.Inverse
/-!
# Time layers in logarithm norm
Normalize at held markers. Holds even for insertions at multiple coincident
stencil roots with disjoint slots (not convergent-contact claims).
-/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Mark
open Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix
open scoped Topology BigOperators
variable {n:Side}{ι U:Type}{J K S T:Finset ι}{D k:ι→ℕ}{i j e r h N m l:ℕ}{G:Gauge}{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
lemma logReverser {w f:Finset ι→ Ink U} [DecidableEq ι](p:w ∅=1)(q:f ∅=0)(ht:∀ S≠∅,
      f S=w S-(S.card:ℝ)⁻¹ • ∑ j∈ S.powerset.erase S,(j.card:ℝ) • (f j*w (S\j))): Equation w f:=by
    refine ⟨p,q,?_⟩; funext S; by_cases z:S=∅; · subst S; rw [shells_emp]; simp [dial]
    rw [dial,shells,←Finset.sum_erase_add _ _ (show S∈ S.powerset by simp), Finset.sdiff_self,p,mul_one,dial, ht S z,smul_sub,← Nat.cast_smul_eq_nsmul ℝ S.card ((S.card:ℝ)⁻¹ • _), smul_smul,mul_inv_cancel₀ (by exact_mod_cast (show S.card≠0 by simp [z])),one_smul]; simp_rw [← smul_mul_assoc,Nat.cast_smul_eq_nsmul]; conv_rhs=>rw [show (∑ x∈S.powerset.erase S,dial f x*w (S\x))=∑ x∈S.powerset.erase S,x.card • f x*w (S\x) from rfl]; abel_nf

abbrev thalamus (D:ι→ℕ)(U:Type):=(S:Finset ι)→ Layers (Pen D S) U
def PalsT (k:ι→ℕ)(P:thalamus D U): Prop:= ∀ S,stops (mass k S) (P S) ∧ ∀ j i,Pure (P S j i)
lemma under_pen (P:Layers (Pen D S) U)(p:stops i P)(v: Case D) : stops i (fun j=> pPly v S (P j)):=fun i j k x=>funext fun v'=>by change touch v S (P i j k v')= _; rw [p i j k x, Pi.zero_apply,map_zero]; rfl
section
variable {Y X:Layers V U}
structure Lit (l:ℕ)(Y:Layers V U) : Prop where
    stop : stops l Y
    shine_: ∀ i j,Pure (Y i j)
omit [NormedSpace ℝ V] in
lemma Lit.plus (h:Lit l Y)(q:Lit l X): Lit l (Y+X):=⟨fun i j v hv=>by rw [Pi.add_apply,Pi.add_apply,Pi.add_apply,h.stop i j v hv,q.stop i j v hv,add_zero],fun i j r=>(h.shine_ i j r).add (q.shine_ i j r)⟩
lemma Lit.μ (h: Lit l Y)(c:ℝ): Lit l (c • Y):=⟨fun i j v hv=>by rw [Pi.smul_apply,Pi.smul_apply,Pi.smul_apply,h.stop i j v hv,smul_zero],fun i j r=> (h.shine_ i j r).smul c⟩
lemma Lit.sub (p:Lit l Y)(q:Lit l X): Lit l (Y-X):=by rw [sub_eq_add_neg,← neg_one_smul ℝ]; exact p.plus (q.μ _)
omit [NormedSpace ℝ V] in
lemma Lit.zero: Lit l (0:Layers V U):= ⟨fun _ _ _ _=>rfl,fun _ _ _=>Blue.Smooth.zero⟩
omit [NormedSpace ℝ V] in
lemma Lit.sum {P:ι→Layers V U}{S:Finset ι}(p:∀ i∈S,Lit l (P i)):Lit l (∑ i∈S,P i):=by classical
                                                                                induction S using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact Lit.zero | @insert i s h ih=> rw [Finset.sum_insert h]; exact (p _ (Finset.mem_insert_self ..)).plus (ih fun j hj=> p j (Finset.mem_insert_of_mem hj))
end

section
variable [Fintype U]
abbrev skyVal (A:Case D)(p : Layers (Pen D S) U)(j:ℕ): Ink (Option U):= ramp (fun i=> pPly A S (p i)) j
variable {X Y:Layers (Pen D S) U}
lemma skyV_add (p: Lit l X)(q:Lit l Y)(A): skyVal A (X+Y) l=skyVal A X l+ skyVal A Y l:=by
   apply lamp_ext; intro j e; rw [map_add,map_add,glance (under_pen X p.stop A),glance (under_pen Y q.stop A),glance (under_pen (X+Y) (p.plus q).stop A),Pi.add_apply,map_add,Pi.add_apply]; exact visible_add (finite_stops (under_pen X p.stop A) j e) (finite_stops (under_pen Y q.stop A) j e)
lemma skyV_μ (p:Lit l X)(c:ℝ)(A): skyVal A (c • X) l=c • skyVal A X l:=by
   apply lamp_ext; intro j e; rw [coeff_smul, map_smul,glance (under_pen X p.stop A),glance (under_pen _ (p.μ c).stop A),Pi.smul_apply,map_smul,Pi.smul_apply]; exact visible_μ (finite_stops (under_pen X p.stop A) j e) c
lemma skyV_sub (p:Lit l X)(q:Lit l Y)(A): skyVal A (X-Y) l=skyVal A X l- skyVal A Y l:=by rw [sub_eq_add_neg,← neg_one_smul ℝ Y,skyV_add p (q.μ _),skyV_μ q,neg_one_smul ℝ,sub_eq_add_neg]
lemma skyV_zero {A:Case D}: skyVal A (0:Layers (Pen D S) U) l=0:=by simpa only [zero_smul] using skyV_μ (X:=(0:Layers (Pen D S) U)) (l:=l) Lit.zero 0 A
lemma skyV_sum {V':Type}{P:V'→Layers (Pen D S) U}{Z:Finset V'}(A)(p:∀ i∈Z,Lit l (P i)): skyVal A (∑ i∈Z,P i) l= ∑ i∈Z,skyVal A (P i) l:=by
    classical
    induction Z using Finset.induction_on with
    | empty=> simp only [Finset.sum_empty]; exact skyV_zero
    | @insert i Z h ih=>
        have ht i' (q:i'∈Z):= p i' (Finset.mem_insert_of_mem q); rw [Finset.sum_insert h,Finset.sum_insert h,skyV_add (p _ (Finset.mem_insert_self ..)) (Lit.sum ht),ih ht]
end
variable [DecidableEq ι]
noncomputable def turnTLog (P:thalamus D U)(S:Finset ι): Layers (Pen D S) U:= if _h:S=∅ then 0 else
    P S - (S.card:ℝ)⁻¹ • ∑ j∈S.powerset, if w:j⊆ S ∧ j≠ S then (j.card:ℝ) • foamT w.1 (turnTLog P j) (P (S\j)) else 0
termination_by S.card
decreasing_by exact Finset.card_lt_card (lt_of_le_of_ne w.1 w.2)
lemma flamL (P:Layers (Pen D J) U)(Q:Layers (Pen D (S\J)) U)(h:J⊆ S)(p:Lit (mass k J) P)(q:Lit (mass k (S\J)) Q) : Lit (mass k S) (foamT h P Q):=by rw [stairK k h]; exact ⟨foamT_stop h P Q p.stop q.stop,foamT_pure h P Q⟩
lemma tripLit (P:thalamus D U)(S:Finset ι)(p:∀ S,Lit (mass k S) (P S))(h:∀ J⊂S,Lit (mass k J) (turnTLog P J))(j): Lit (mass k S) (if w:j⊆S∧j≠S then (j.card:ℝ) • foamT w.1 (turnTLog P j) (P (S\j)) else 0):=by
    split
    next W=> exact (flamL _ _ W.1 (h _ (lt_of_le_of_ne W.1 W.2)) (p _)).μ _
    exact Lit.zero
lemma turn_stop (P:thalamus D U)(v:∀ S,Lit (mass k S) (P S)):∀ S,Lit (mass k S) (turnTLog P S):=by
    intro S; induction S using Finset.strongInduction with
    | H S ih=>
        rw [turnTLog]; split
        · exact Lit.zero
        exact (v _).sub ((Lit.sum (fun i _=>tripLit P S v ih i)).μ _)

section
variable [Fintype U]
lemma flashEra (P:thalamus D U)(A:Case D)(p:∀ S,Lit (mass k S) (P S))(x:skyVal A (P ∅) (mass k ∅)=1): Equation (fun S=>skyVal A (P S) (mass k S)) (fun S=>skyVal A (turnTLog P S) (mass k S)):=by
    have hu : turnTLog P ∅=0:=by rw [turnTLog, dif_pos rfl]
    refine logReverser x (hu.symm ▸ skyV_zero) (fun S z=>?_)
    have h j:=turn_stop P p j; have hf j:= tripLit P S p (fun i _=> h i) j; rw [turnTLog,dif_neg z,skyV_sub (p _) ((Lit.sum (fun i _=> hf i)).μ _),skyV_μ (Lit.sum (fun i _=> hf i)),skyV_sum A (fun i _=> hf i)]
    congr 2; rw [← Finset.sum_erase_add _ _ (show S∈ S.powerset by simp)]; rw [dif_neg (show ¬(S⊆S∧S≠S) by simp),skyV_zero,add_zero]; apply Finset.sum_congr rfl; intro j hj; have hh:j⊆ S∧j≠S:=by simpa only [Finset.mem_erase,Finset.mem_powerset,and_comm] using hj
    rw [dif_pos hh,skyV_μ (flamL _ _ hh.1 (h j) (p _)),skyVal,fpT,stairK k hh.1]; exact congr_arg ((_ • ·)) (ramp_joint _ _ (under_pen _ (h j).stop A) (under_pen _ (p _).stop A))
end
end YM.WilsonCoeffUV.Wheel.Mark
