import YM.OPE.Compatible.Village.Town
/-!
# Norm ledger for the nested OPE logarithmic bounds. No loss. Using a single budget time that grows from root and dominates each node log. Needs tendsto even on ultraselections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel Arcade Cov Cov.Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X)
   {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(p:X→ S.Tag)
variable {η M:ℝ}
local notation "U"=> heart X
local notation "U'"=> rest (heart X)
-- geometry and positivity
section energy
variable {s:X→ℝ}{x:X→ E4} (L:Layout D M η s x)(h: ⊥∈heart X)
include L h
lemma earns_scale (k:ℕ) : fuel D p 0 (k:ℝ) s = (padding D (heart X) p k s)⁻¹:=by
    have he:= L.pos _ h; let t v:= Real.log (s v)
    have hP (v:X)(h:v∈U') : jump D t v= Real.log (rat D s v):= by
       have hp:=L.pos _ ((mem_erase.mp h).2); unfold jump t rat; exact (Real.log_div hp.ne' (ne_of_gt (hp.trans_le (L.scales _ h)))).symm
    have hA (s:ℝ)(h:0<s)(a:ℝ):s^a=Real.exp (a*Real.log s):=by rw [Real.rpow_def_of_pos h,mul_comm]
    have hb : volume D U (fun i=> (p i.val).1) s = Real.exp (payload D U p t):=by
        unfold volume payload; rw [Real.exp_sum]; refine prod_congr rfl fun i _=>?_; dsimp only [Sigma.fst,picked] -- change
        let v:= par D i.val; let m:=(p i.val).1; have hu:= L.pos v ((on_brim ..).1 i.2|>.2.2); change (s v)^m=Real.exp ((m:ℝ)*Real.log (s v)); rw [Real.exp_nat_mul, Real.exp_log hu]
    unfold fuel padding costed; rw [hb, ← Real.exp_log he]; -- no rew because s other? adjust
    have hf : ∏ v∈ U',(rat D s v)^(-(portion D U v p:ℝ)-(0:ℝ)) = Real.exp (-∑ v∈ U',(portion D U v p:ℝ)*jump D t v):=by
        rw [← Finset.sum_neg_distrib,Real.exp_sum]; refine prod_congr rfl fun v hv=>?_; rw [sub_zero,hA (rat D s v) (L.ratios D hv).1,hP v hv,neg_mul]
    rw [hf,hA _ (Real.exp_pos _),Real.log_exp,inv_div,payload_len D p U (tall h), ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_sub]; congr 1; unfold t; ring
end energy
-- exact same time on all nested subtrees
-- product: log(1/s) all positive eventually. effective integer bound. when T padding theorem works

def shine (s:X→ℝ):= ∏ v∈heart X, (1+Real.log ((s v)⁻¹))
section psi
variable {φ:Filter I} {s:I→X→ℝ}{x:I→ X→ E4}(h:∀ᶠ i in φ,Layout D M η (s i) (x i))
variable (hg:Tendsto (fun i=>s i ⊥) φ (𝓝[>]0))(h0: ⊥∈heart X)
include D h hg
lemma reaches_min {v:X}(hv:v∈heart X): Tendsto (fun i=>s i v) φ (𝓝[>]0):=by
    have hp :∀ᶠ i in φ,0 < s i v:= h.mono fun _ hi=>hi.pos _ hv
    exact tendsto_nhdsWithin_iff.mpr ⟨squeeze_zero' (hp.mono fun _ h=>h.le) (h.mono fun _ hi=>hi.earlier D hv bot_le) (hg.mono_right nhdsWithin_le_nhds),hp⟩
lemma shines_up (v:X)(hv:v∈heart X):∀ᶠ i in φ, 1+run (s i v) ≤ shine (s i):=by
    filter_upwards [(eventually_all_finset (heart X)).mpr fun v hv=>(run_towards (reaches_min D h hg hv)).eventually_ge_atTop 0] with i hi
    have hp (v:X) (hv:v∈heart X):1 ≤ 1+Real.log (s i v)⁻¹:=(by simp only [Real.log_inv]; exact le_add_of_nonneg_right (hi _ hv))
    unfold shine; unfold run; rw [← Real.log_inv]; let F v := 1+Real.log (s i v)⁻¹; have hF : 1 ≤ ∏ v ∈ (heart X).erase v,F v:= Finset.one_le_prod (fun a ha=> hp _ (mem_of_mem_erase ha)); rw [← mul_prod_erase (heart X) (fun i'=>_) hv]; exact le_mul_of_one_le_right (zero_le_one.trans (hp v hv)) hF
include h0
lemma dawn: Burst D U φ (shine ∘ s) s:=by
    have ht: Tendsto (shine∘s) φ atTop:=by
       apply tendsto_atTop.mpr; intro k; filter_upwards [shines_up D h hg _ h0,(run_towards hg).eventually_ge_atTop k] with i hi hh; exact le_trans (le_trans hh (le_add_of_nonneg_left zero_le_one)) hi
    refine ⟨fun η hη=>?_,?_⟩
    · refine ⟨tall h0,ht,hη,fun i hi=> reaches_min D h hg hi,fun i hi=> ?_,h.mono fun i hi v hv y h=> hi.earlier D hv h⟩
      exact (Score.time ht).pointwise ((shines_up D h hg i hi).mono fun i hi=> le_trans (le_add_of_nonneg_left zero_le_one) hi) ((run_towards (reaches_min D h hg hi)).eventually_ge_atTop 0)
    filter_upwards [h,(eventually_all_finset U).2 (shines_up D h hg)] with i hi hT v hv; exact (le_of_le_of_eq (Real.exp_le_exp.mpr (by have hh:=hT v hv; unfold run at hh; change -shine _≤_; linarith only [hh])) (Real.exp_log (hi.pos _ hv)))
omit h0 hg in
lemma basisR (hh:0 ≤ M):∀ᶠ i in φ,Ridge (s i) η (envelope X M) D U (away (x i) (x i ⊥)):=by
    filter_upwards [h] with i hi; refine ⟨sub_self _,fun v w hv _ hl=> ?_,fun v w _ _ hv hw=>?_⟩
    · unfold away; rw [sub_sub_sub_cancel_right,norm_sub_rev]; exact hi.reaches D hh hv hl
    unfold away; rw [sub_sub_sub_cancel_right]; exact hi.fork D hv hw
end psi
end YM.OPE.Arboreal.Trace
