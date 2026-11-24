import YM.OPE.Backup.Pigment
/-!
# Preserve radius costs under linear superposition at each slot
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Muster.Pigment
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup
open scoped Topology BigOperators Classical
variable {I J : Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n:Side}
local notation "X"=> (Bud I)
local notation "Y"=> (Bud J)
variable (A:I→J) (s:I→ℂ) (R:Rep G n)
local notation "F"=> homL A s
variable {w:I→ℝ} {w':J→ℝ}{y x z:ℝ} {ξ:Type*}
lemma largesse (hp:∀ i,w' (A i)*‖s i‖≤w i)(hx:∀ i,0≤w' i)(hw:∀ i,0 ≤ w i)(p:(Bud I).Mode): ∑ i:(Y).Mode, Poly.toll w' i*‖(mark A s p).part i‖ ≤ Poly.toll w p:=by
   rw [sum_eq_single (batch A p),symbol]; rotate_left
   · intro i _ hi; rw [symbol]; split_ifs <;>simp only [Poly.part_send,hi,if_false,norm_zero,mul_zero, Poly.part_nil]
   · simp
   split; rename_i he; rw [Poly.part_send,if_pos rfl,norm_prod]; change (∏ i∈p.val.image A,w' i)*_ ≤ _; rw [prod_image he, ← prod_mul_distrib]; exact prod_le_prod (fun i _=>mul_nonneg (hx _) (norm_nonneg _)) (fun i _=> hp _)
   exact (by rw [Poly.part_nil,norm_zero,mul_zero]; exact prod_nonneg fun i _=> hw _)
lemma heritage {v:ξ→Poly X}(hf:Loci w v x)(hp:∀ i,w' (A i)*‖s i‖≤w i)(hx:∀ i,0≤w' i)(hw:∀ i,0 ≤ w i): Loci w' (F ∘ v) x:=by
   obtain ⟨u,he,h,hv⟩:=hf; let U (i:(Y).Mode):= ∑ j:(X).Mode,u j*‖(mark A s j).part i‖
   have hz(i):0≤U i:=sum_nonneg fun i _=> mul_nonneg (he _) (norm_nonneg _)
   refine ⟨U,hz,fun x i=>?_,?_⟩
   · rw [comp_apply,part_of]; refine (norm_sum_le ..).trans (sum_le_sum (fun i hi=>?_)); rw [norm_mul]; apply mul_le_mul_of_nonneg_right (h ..) (norm_nonneg _)
   unfold wordsPrice U; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine le_trans (sum_le_sum (f:=fun j=>∑ i:(Y).Mode,Poly.toll w' i* (u j*‖(mark A s j).part i‖)) ?_) hv; intro i _
   simp_rw [mul_left_comm _ (u i) _,← mul_sum]; exact (mul_le_mul_of_nonneg_left (largesse _ _ hp hx hw i) (he i)).trans_eq (mul_comm ..)
lemma TowedL {ι:Type*}{p:ι→ Support n}{f:ι→ξ→Poly X}{b:ℕ}(h:Towed w p f b z x)(hp:∀ i,w' (A i)*‖s i‖≤w i)(hx:∀ i,0≤w' i)(hw:∀ i,0 ≤ w i): Towed w' p (fun i=>F ∘ f i) b z x:=by obtain ⟨u,h1,h2,h3⟩:=h; exact ⟨u,h1,h2,fun i=> heritage _ _ (h3 i) hp hx hw⟩
variable {o:I→Site n}{o':J→Site n}
variable (hO:∀ i,s i ≠ 0 → o' (A i)=o i)
variable {H:Support n→ Config G n→Poly (Bud I)}{K:Box n→ Config G n→Poly (Bud I)}
-- parse space
include hO
lemma borneL {f:Config G n→Poly X}{p:Support n}(hh:Borne o p f x):Borne o' p (F ∘ f) x:=by
   refine ⟨fun a b ht he=> congr_arg F (hh.home _ _ ht he), fun u Q=> congr_arg F (hh.turns ..),fun i=>?_,fun Q i hi=> not_not.mp (fun he=> ?_)⟩
   · simp_rw [comp_apply,part_of]; exact Finset.measurable_sum _ (fun i _=> (hh.me i).mul_const _)
   obtain ⟨a,hf,hx⟩:= source_lit A s (f Q) i he; have hp:= hh.place a Q hf; obtain ⟨_,heq,hV⟩:= remembered A s a hx; apply hi; intro j hj; obtain ⟨k,hk,rfl⟩:=mem_image.mp (show j∈(batch A a).val from heq ▸ (show j∈i.val from hj)); change o' (A k)∈p; exact hO _ (hV _ hk) ▸ hp (mem_image_of_mem _ hk)
lemma cartonL (h:Carton o H K x) : Carton o' (fun i=>F ∘ H i) (fun i=>F ∘ K i) x:= by
   refine ⟨fun i=> ⟨⟨borneL _ _ hO (h.exp i).1.toBorne, fun U hh=>(h.exp i).1.permits U ?_,fun U=> quiet A s (H i U) ((h.exp i).1.sil U)⟩,fun U=> highly A s (H i U) ((h.exp i).2 U)⟩,
           fun i=> ⟨⟨borneL _ _ hO (h.flag i).1.toBorne, fun U hh=>(h.flag i).1.permits U ?_⟩,fun U=> highly A s (K i U) ((h.flag i).2 U)⟩ ⟩
   all_goals intro he; apply hh; rw [comp_apply,he,map_zero]
omit hO
variable (H K)
abbrev residents (i:J):= univ.filter (fun k=>A k=i)
lemma MachL (u:I→ℂ) : F (Mach X u) = Mach Y (fun i=>∑ j∈ residents A i,s j*u j):= by
   unfold Mach; rw [map_sum]; simp_rw [fires]; ext i; rw [Poly.part_sum,Poly.part_sum]; by_cases hp:∃ k,i=(Y).fire k
   · obtain ⟨k,rfl⟩:=hp; simp [Poly.part_send,eq_comm,residents,Finset.sum_filter]
   push Not at hp; simp [Poly.part_send,hp]
lemma fieldL (v:Box n→Poly X)(p:Support n): F (field v p)= field (F ∘ v) p:=by
   unfold field; rw [map_sum]; refine sum_congr rfl fun p _=>?_ ; unfold grid; split; exact preserves_prod ..; exact map_zero _
lemma beadL (p:ℂ): F (Poly.bead X p)=Poly.bead Y p:= by
    change F (Poly.send ((Bud I).quiet) p)= Poly.send ((Bud J).quiet) p; rw [sent,mark,(show (X).quiet.val=(∅:Finset I) from rfl),prod_empty]; ext x; simp [Poly.one_part]
lemma restoreL (α:I→ Config G n→ℂ)(β:I→Res G n)(M:Config G n)(h: ∀ i:Support n,(H i M).part (X|>.quiet)=0) : F (restore R α β H K M)= restore R (fun i=>∑ j∈ residents A i,s j • α j) (fun i=>∑ j∈ residents A i,s j • β j) (fun i=>F ∘ H i) (fun i=>F ∘ K i) M :=by
    let g:= Mach X (fun i=>α i M); unfold restore; rw [map_smul,preserves,passes A s _ (show (g+_).part (X|>.quiet) = _ from (by rw [Poly.part_plus,Poly.part_sum,mute]; exact zero_add _|>.trans (sum_eq_zero fun i _=>h i))), map_add,MachL, map_sum, fieldL]; simp_rw [Finset.sum_apply]; congr 3
    funext i; simp only [comp_apply]; erw [map_add,map_add,MachL,show F (bar R.activities X M i)=bar R.activities Y M i from beadL ..]; rfl
end YM.MergeProof.Ribbons.ManyCopies.Muster.Pigment
