import YM.OPE.Compatible.Cum.Six
/-!
# Arithmetic relabels. stack freezing
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter Set MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin LinearMap
open Lattice Laurent RG Precision Flume Flume.Script Flume.Page
variable {I J E R:Type}{e d x y t:ℕ}{N:Side}
-- compose equiv under script
def slice (p:Fin e ≃ Fin d)(A:Script I e): Script I d:=fun B=> A (B ∘ p)
@[simp] lemma slice_fee (p:Fin e ≃ Fin d)(A:Script I e){c:ℝ}(h:soot t A c): soot t (slice p A) c:=by
     have he:e=d:=by simpa only [Fintype.card_fin] using Fintype.card_congr p
     subst d; exact swing_fee h p
lemma slice_pay (p:Fin e ≃ Fin d)(A: Script I e)(u:Fin d→deck I N)(a:Site N): scribe a (slice p A) u= scribe a A (u ∘ p):=by
     have he:e=d:= calc
        e=Fintype.card (Fin e):=(Fintype.card_fin _).symm
        _=Fintype.card (Fin d):= Fintype.card_congr p
        _ = _:=Fintype.card_fin _
     subst d; exact rotating p A u a
-- freeze equivalence old 0 moved to end of active. rotate by swapping 0 and d, preserves active order almost but all identical. d=0 ok.
private lemma fact (e d:ℕ): e+d+1=e+1+d:= by omega
def beginC (e d:ℕ) : Fin (e+d+1) ≃ Fin (e+1+d):= (wand e d (Fin.last d)).trans (finCongr (fact e d))
lemma begin_pay (e d:ℕ)(x y:R): cue x y (e+1) d ∘ beginC e d=Fin.cons y (cue x y e d):=by
     let k:= pinT (e:=e) (Fin.last d); let S:= beginC e d; have hh:(S 0).val = d:=by unfold S beginC wand; simp only [Equiv.trans_apply,Equiv.swap_apply_left,finCongr_apply,Fin.val_cast, pinT,Fin.val_last]
     funext i; refine Fin.cases ?_ (fun i=>?_) i
     · change cue x y (e+1) d (S 0)=_; rw [cue,if_neg (by rw [hh]; omega)] -- not_lt
       rfl
     change cue x y (e+1) d (S i.succ)=cue x y e d i; by_cases h:i.succ=k
     · have ht : i.val < d:= by change Fin.succ i=k at h; have ht: i.val+1=d:=congr_arg Fin.val h; omega
       rw [cue,cue,if_pos ht,if_pos]; rw [h]; unfold k S beginC wand; simpa using! (show 0<d from (Nat.zero_le i.val).trans_lt ht)
     have hv:i.val+1≠d:=fun e=>h (Fin.ext e); unfold S beginC; rw [Equiv.trans_apply, show wand e d (Fin.last d) i.succ=i.succ from Equiv.swap_apply_of_ne_of_ne i.succ_ne_zero h]; unfold cue; rw [finCongr_apply,Fin.val_cast,Fin.val_succ]; split <;> split <;> first|rfl|omega
-- merge e+d (a) active d and y+t extras; Target e+y+(d+t). use first live extras prepended? source uses Fin.append. easiest piecewise corank via ⊕ shuffle FinSum
local notation "U" => Fin
-- normalized category a=Fin(e+d) decomposes into d ⊕ e. implement val via casts
def sliceSep (e d:ℕ) : Fin (e+d)≃(Fin d⊕Fin e):= (finCongr (Nat.add_comm e d)).trans finSumFinEquiv.symm
lemma cut_pay (a b:R)(e d:ℕ)(x:Fin (e+d)): cue a b e d x = (sliceSep e d x).elim (fun _=>a) (fun _=>b):=by
    obtain ⟨i|i,hi⟩:= (sliceSep e d).symm.surjective x -- direction
    · rw [← hi,(sliceSep e d).apply_symm_apply,Sum.elim_inl,cue,if_pos]; unfold sliceSep; simp
    rw [←hi,(sliceSep e d).apply_symm_apply,Sum.elim_inr,cue,if_neg]; unfold sliceSep; simp
-- equivalence (d+e ⊕y+t) slots reorder
private def joist (A B C D:Type): (A ⊕ B) ⊕ C ⊕ D ≃ (A⊕ C)⊕ B ⊕ D:= Equiv.sumSumSumComm A B C D -- name
def plank (e d y t:ℕ): Fin (e+d+(y+t))≃Fin (e+y+(d+t)):=
     finSumFinEquiv.symm |>.trans ((sliceSep e d).sumCongr (sliceSep y t))|>.trans (joist ..)|>.trans (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)|>.trans (sliceSep (e+y) (d+t)).symm
lemma plank_pay (a b:R)(e d y t:ℕ):cue a b (e+y) (d+t) ∘ plank e d y t= Fin.append (cue a b e d) (cue a b y t):=by
    ext1 i; refine Fin.addCases ?_ ?_ i
    · intro i; rw [Fin.append_left]; obtain ⟨i|i,rfl⟩:= (sliceSep e d).symm.surjective i <;> simp [cut_pay, Function.comp_apply,plank,joist]
    intro i; rw [Fin.append_right]; obtain ⟨i|i,rfl⟩:=(sliceSep y t).symm.surjective i <;>simp [cut_pay,Function.comp_apply,plank,joist]
end YM.OPE.Libra.Shell
