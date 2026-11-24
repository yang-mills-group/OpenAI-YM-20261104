import YM.Lodestar.Twin
import YM.MergeProof.Paddle
/-!
 `Served` marker price under the doubled-tags map, with weights w in
 both copies, w^2 on unfolded modes. No projection of labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Lodestar
open Finset Function Marker Push GridApprox.Nil Lattice Wilson RG Ac MergeProof Accent
open scoped BigOperators Classical Topology
variable {V I Y : Type} [Fintype V] [DecidableEq V] {G:Gauge} {n:Side}

lemma two_toll (w:V→ℝ)(i:(Marks V).Mode) : Poly.toll (w ∘ Prod.fst : V×Bool→ℝ) (two i) = Poly.toll (fun j=> w j^2) i:=by
   unfold Poly.toll; change (∏ j ∈ i.val ×ˢ (univ:Finset Bool),(w ∘ Prod.fst) j)=_; rw [Finset.prod_product]; exact Finset.prod_congr rfl fun j _=> by simp [sq]

def transfer (u:Sheet (Marks V)): Sheet (Marks (V×Bool)):= extend two u 0
lemma at_two (u:Sheet (Marks V))(i:(Marks V).Mode): transfer u (two i)=u i:= two_inj.extend_apply ..
lemma transfer_miss (u:Sheet (Marks V))(i:(Marks (V×Bool)).Mode)(h:∀ j:(Marks V).Mode,i≠two j):transfer u i=0:=by rw [transfer,extend_apply'];rfl;rintro ⟨x,hx⟩;exact h x hx.symm
lemma price_transfer (w:V→ℝ)(u:Sheet (Marks V)): wordsPrice (w ∘ Prod.fst) (transfer u)=wordsPrice (fun j=> w j^2) u:=by
  unfold wordsPrice
  -- filter the finite univ to image
  let E: Finset (Marks (V×Bool)).Mode:= univ.image two
  have he : E ⊆ univ:=Finset.subset_univ _
  rw [← Finset.sum_subset he (f:=fun i=>Poly.toll (w ∘ Prod.fst) i*transfer u i) ?_]
  · unfold E; rw [Finset.sum_image];exact Finset.sum_congr rfl fun i _=> by rw[two_toll,at_two]
    exact fun _ _ _ _ h=>two_inj h
  intro i _ hh; rw [transfer_miss u i (fun j h=>hh (by rw [h];exact mem_image_of_mem _ (mem_univ _))),mul_zero]

lemma loci_duplicate (Y:Type) (w:V→ℝ)(f:Y→Poly (Marks V)){c:ℝ}(h:Loci (fun j=>w j^2) f c):Loci (w ∘ Prod.fst) (duplicate V ∘ f) c:=by
  obtain ⟨a,hx,hA,hP⟩:= h
  refine ⟨transfer a,?_,fun y j=> ?_,(price_transfer w a).trans_le hP⟩
  · intro i; by_cases he:∃ j,i=two j
    · obtain ⟨j,h⟩:=he; rw [h,at_two]; exact hx _
    rw [transfer_miss _ i (fun j h=>he ⟨j,h⟩)]; rfl
  by_cases he:∃ i,j=two i
  · obtain ⟨i,rfl⟩:=he; dsimp only[Function.comp_apply]; rw [at_two,seal_part]; exact hA ..
  change ‖(duplicate V (f y)).part _‖ ≤ _
  rw [seal_miss _ j (fun i h=>he ⟨i,h⟩),transfer_miss _ j (fun i h=>he ⟨i,h⟩),norm_zero]

lemma towed_duplicate (w:V→ℝ){M:ℕ}{s:I→Support n}{f:I→Y→Poly (Marks V)}{e c:ℝ}(h:Towed (fun j=>w j^2) s f M e c):Towed (w ∘ Prod.fst) s (fun i=>duplicate V ∘ f i) M e c:=by
   obtain ⟨u,h,ht,hv⟩:=h; exact ⟨u,h,ht,fun i=>loci_duplicate Y w _ (hv i)⟩

lemma large_duplicate {p: Poly (Marks V)} (h:p.part (Marks V|>.quiet)=0): rises (duplicate V p):=by
   intro i hi
   obtain ⟨j,rfl⟩:∃ j,i=two j:= of_not_not (fun he=>hi (seal_miss _ _ (fun j h=>he ⟨j,h⟩)))
   suffices he:1 ≤ j.val.card by rw [two_card]; omega
   refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr fun he=>?_)
   apply hi; rw [seal_part,show j=(Marks V).quiet from Subtype.ext he,h]

lemma borne_duplicate {o:V→Site n}{s:Support n}{f:Config G n→Poly (Marks V)}{t:ℝ}(h:Borne o s f t): Borne (o ∘ Prod.fst) s (duplicate V ∘ f) t:=by
   constructor
   · intro U D hp hT; exact congr_arg (duplicate V) (h.home U D hp hT)
   · intro g U; exact congr_arg (duplicate V) (h.turns g U)
   · intro i
     by_cases he:∃ j,i=two j
     · obtain ⟨j,rfl⟩:=he; simp_rw [Function.comp_apply,seal_part]; exact h.me _
     simp_rw [Function.comp_apply,seal_miss _ _ (show ∀ j,i≠two j from fun j h=> he ⟨j,h⟩)]; exact measurable_const
   intro U i hi
   change (duplicate V (f U)).part i=0
   by_cases he:∃ j,i=two j
   · obtain ⟨j,rfl⟩:=he; rw [seal_part]; apply h.scope
     intro h'; apply hi; rintro ⟨v,b⟩ hv; exact h' ((two_test j v b).mp hv)
   exact seal_miss _ i fun j h=>he ⟨j,h⟩

lemma burns_duplicate {o:V→Site n}{s:Support n}{f:Config G n→Poly (Marks V)}{t:ℝ}(h:Burns o s f t): Burns (o ∘ Prod.fst) s (duplicate V ∘ f) t ∧ ∀ U,rises ((duplicate V ∘ f) U):=by
   refine ⟨⟨borne_duplicate h.toBorne, fun U hv=> h.permits _ (fun ht=> hv (by rw [Function.comp_apply,ht,map_zero])),fun U=>?_⟩,fun U=> large_duplicate (h.sil U)⟩
   rw [Function.comp_apply,← two_quiet,seal_part,h.sil]

lemma flow_duplicate {o:V→Site n}{s:Box n}{f:Config G n→Poly (Marks V)}{t:ℝ}(h:Flow o s f t): Flow (o ∘ Prod.fst) s (duplicate V ∘ f) t:=by
   exact ⟨borne_duplicate h.toBorne,fun U hv=> h.permits _ (fun ht=>hv (by rw [Function.comp_apply,ht,map_zero]))⟩
end YM.Lodestar
