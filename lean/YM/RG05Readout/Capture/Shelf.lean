import YM.RG05Readout.Capture.Pantry
/-!
# Whole-shot aggregation (before Serves)

When repainting a countertag, need its pepper, K response, and log debris from
all ancestors. This carries even when distinct origins someday share the same
slot, via fiber-card costs (NOT total marker count).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge} {n:Side}{m p N d:ℕ}{V W : Type}[DecidableEq V] [Fintype V][DecidableEq W][Fintype W] {R:Census V}{B:Census W}{a b c e t y z α β f E:ℝ}
variable {X:Rep G n} {P:V→ Three G n}{o:V→ Site n}{w:V→ℝ}{F:Config G n→ Poly R}
variable {δ:V→W}{h:License B R δ} (v:V→ℂ)
local notation "ν" => (feed v h)
local notation "Ω"=> fun j:W=> (Finset.univ: Finset V).filter fun i=> δ i=j
local notation "Σ₁"=> combine δ v

-- internal helper to calculate solo image directly. Can project all non-quiet solo.
omit [Fintype W] in
lemma solo_feed (X:Poly R)(j:W): (ν X).part (B.fire j)=∑ i∈ Ω j,v i* X.part (R.fire i):=by
    rw [parts_of_feed]
    let pR:= R.fire; let S:=(Ω j).image pR
    rw [← Finset.sum_subset (Finset.subset_univ S), show S= _ from rfl, show S=Finset.image pR (Ω j) from rfl, sum_image]; rotate_left
    · intro i _ j _ he; exact Finset.singleton_injective (congr_arg Subtype.val he)
    · intro i _ hi; unfold move; split
      next hg=>
       rw [Poly.part_send]; split
       next ht=>
        have h':i.val.card=1:= hg.keep_count.symm.trans (ht ▸ Finset.card_singleton _)
        obtain ⟨k,hk⟩:= Finset.card_eq_one.mp h'; have hp:i=pR k:=Subtype.ext hk
        apply False.elim (hi ?_); apply mem_image.mpr; refine ⟨k,Finset.mem_filter.mpr ⟨mem_univ _,?_⟩,hp.symm⟩
        have he:{j}= i.val.image δ:= congr_arg Subtype.val ht; rw [hk,image_singleton] at he; exact Finset.singleton_injective he.symm
       next=> rfl
      next=> rfl
    refine sum_congr rfl (fun i hi=>?_); rw [move]; split
    next ht=> rw [Poly.part_send, if_pos ?_]; exact congr_arg (·* X.part _) (Finset.prod_singleton ..); exact Subtype.ext (by dsimp only [pR,Census.fire,Lit.climb]; rw [Finset.image_singleton,(mem_filter.mp hi).2])
    next ht=> exact False.elim (ht (dark_one _))

omit [DecidableEq V] [Fintype W] in
lemma solo_com {E:Type*}[AddCommGroup E][Module ℂ E] (f:V→E)(j:W): Σ₁ f j=∑ i∈ Ω j,v i • f i:=by
    unfold combine; rw [sum_filter]; refine sum_congr rfl (fun i _=>?_); split; rfl; next H=> rw [zero_smul] -- depends ` classical Prop`
lemma solo_mach (f:V→ℂ): feed v h (Mach R f)= Mach B (Σ₁ f):= by rw [feed_mach]; congr 1; funext j; rw [solo_com,sum_filter]; rfl
variable {ψ:V→Response G n}{q:W→Site n}{w':W→ℝ}
local notation "M"=> (N:ℝ)
local notation "Θ"=> ∀ j:W,(Ω j).card≤N
local notation "ξ"=> ∀ i,w' (δ i)*‖v i‖ ≤ w i/(N:ℝ)
local notation "τ"=> X.p.threshold
omit [DecidableEq V] [Fintype W] in
lemma hook_sales (j:W) : hook X.activities X.p.threshold (Σ₁ ψ j) = ∑ i∈ Ω j,v i • hook X.activities X.p.threshold (ψ i):=by
    let L:Response G n→ₗ[ℂ] (Box n→ Config G n→ℂ):={ toFun:=hook X.activities X.p.threshold,map_add':=fun a b=>hook_add,map_smul':=fun a b=>hook_scale .. }
    rw [solo_com]; change L (∑ i∈_, v i • ψ i)=_; rw [map_sum];simp only [map_smul];rfl
omit [DecidableEq V] [Fintype W] in
lemma garnish_bundle (he:o=q ∘ δ)(hf:Garnish X.p o ψ w E e) (hh:0<N)(hg:0 ≤ e)
    (_:∀ i,0<w' i)(hV:ξ) (hT:Θ) : Garnish X.p q (Σ₁ ψ) w' E e:=by
    choose f hF hX using hf.fee
    refine ⟨fun i k=> ?_,fun i k hk=> ?_, fun i=>?_⟩
    · rw [solo_com,Finset.sum_apply]
      refine ⟨fun U V hh h'=>?_,fun a b=> ?_,?_,fun U hU=>?_⟩
      · rw [Finset.sum_apply,Finset.sum_apply]; exact sum_congr rfl (fun j _=> congr_arg (v j • ·) ((hf.yes j k).sites _ _ hh h'))
      · rw [Finset.sum_apply,Finset.sum_apply]; exact sum_congr rfl (fun j _=> congr_arg (v j • ·) ((hf.yes j k).symmetry ..))
      · rw [show (∑ c∈ Ω i,(v c • ψ c) k)= fun a=>∑ c∈ Ω i,v c • ψ c k a from funext fun a=> Finset.sum_apply a _ _]; exact Finset.measurable_fun_sum _ (fun j _=> (hf.yes j k).borel.const_smul (v j))
      rw [Finset.sum_apply]; refine sum_eq_zero (fun j _=>?_); simp only [Pi.smul_apply,(hf.yes j k).healthy_zero U hU,smul_zero]
    · rw [solo_com,Finset.sum_apply] at hk; obtain ⟨j,hj,hJ⟩:=Finset.exists_ne_zero_of_sum_ne_zero hk
      have hx : o j=q i:=by rw [he,Function.comp_apply,(mem_filter.mp hj).2]
      exact hx ▸ hf.tracks _ k (fun h=> hJ (by simp only [Pi.smul_apply,h,smul_zero])) -- ▸ issue
    let C:=(Ω i); let Y(k:Support n):=∑ j∈ C, ‖v j‖*f j k
    have hM : 0<(N:ℝ):=Nat.cast_pos.mpr hh; let Λ (k:Support n):= Real.exp ((E+1)*coverNumber X.p.B k); have hL k:0 ≤ Λ k:=(Real.exp_pos _).le
    refine ⟨Y,fun k=>⟨Finset.sum_nonneg fun j _=>mul_nonneg (norm_nonneg _) ((hF j k).1),fun U=>?_⟩, ?_⟩
    · rw [solo_com,Finset.sum_apply,Finset.sum_apply]; apply (norm_sum_le ..).trans (sum_le_sum _); intro j _; rw [Pi.smul_apply,Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left ((hF ..).2 U) (norm_nonneg _)
    change ∑ k, Λ k*(w' i*(∑ j∈ C, _)) ≤ e; simp_rw [mul_sum]; rw [Finset.sum_comm]; apply le_trans (b:=∑ _j∈C,e/(N:ℝ)) (sum_le_sum _) _
    · intro j hj; have he:w' i*‖v j‖≤ w j/(N:ℝ):=by rw [← (mem_filter.mp hj).2]; exact hV j
      apply le_trans (b:=(∑ k, Λ k*(w j*f j k))/(N:ℝ)) _ (div_le_div_of_nonneg_right (hX _) hM.le); rw [Finset.sum_div]; apply sum_le_sum; intro k _; rw [← mul_assoc (w' i)]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (hF ..|>.1)) (hL _)).trans_eq (by ring)
    rw [Finset.sum_const,nsmul_eq_mul]; have hS : (C.card:ℝ) ≤ (N:ℝ):=Nat.cast_le.mpr (hT i); exact (mul_le_mul_of_nonneg_right hS (div_nonneg hg hM.le)).trans_eq (by field_simp) -- positivity

omit [Fintype V] in
lemma one_live (ha:Integrable F (prior G _))(i:R.Mode): Integrable (fun U=>(F U).part i) (prior G _):=((Marker.Poly.get i).restrictScalars ℝ).integrable_comp ha
set_option maxHeartbeats 850000 in
lemma Alcove.group (ha:Alcove X P F o w t e c) (hr:X.Lawful α β b y E)(hu:Integrable F (prior G _))
    (he:o=q ∘ δ)(hh:0<N)(hg:0 ≤ e)(hc:0 ≤ c) (hw:∀ i,0<w i) (hP:∀ i,0<w' i)(hV:ξ)(hT:Θ): Alcove X (Σ₁ P) (fun U=> ν (F U)) q w' t e c:=by
    have hW': 1 ≤ (N:ℝ):= (by exact_mod_cast hh); have hN : 0<(N:ℝ):= zero_lt_one.trans_le hW'
    have hY(i): Useful X (P i):=by refine ⟨ha.clef _,ha.price _,?_⟩; rw [← show (fun U=>(F U).part (R.fire i))= _ from funext (ha.tally i)]; exact one_live hu _
    let U i:= v i • P i; have hU(i) : Useful X (U i):= Useful.smul _ _ _ (hY i);
    have hf(i) : Useful X (combine δ v P i):=by rw [solo_com]; exact Useful.family X hr _ U hU
    refine ⟨fun i=>(hf i).normK,fun U=> (feed_quiet ..).trans (ha.value _),fun i U=>?_,fun i=> (hf i).read,?_⟩
    · rw [solo_feed,solo_com,Prod.fst_sum,Finset.sum_apply]; simp_rw [ha.tally]; rfl
    obtain ⟨H,K,ψ,ν',hL,hK,hX,hB,hG,hp,hR,hΨ,hF⟩:= ha.chamber; have hk(i): w' (δ i)*‖v i‖ ≤ w i:=(hV i).trans (div_le_self (hw _).le hW')
    refine ⟨fun i U=> ν (H i U),fun j U=> ν (K j U),Σ₁ ψ, Σ₁ ν', carry h v hL hk hw hP,carry h v hK hk hw hP,fun i=>carry_burns h v he (hX i),fun i=>carry_flow h v he (hB i),garnish_bundle v he hG hh hg hP hV hT,?_,fun i U=> (feed_quiet ..).trans (hR i U),fun i j U'=>?_,?_⟩
    · intro i; rw [solo_com]; refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (hP _).le).trans ?_; rw [Finset.mul_sum]
      let C:=(Ω i); apply le_trans (b:=∑ _ ∈ C,c/(N:ℝ)) (sum_le_sum _) _
      · intro j hj; have hv : w' i*‖v j‖≤ w j/(N:ℝ):=by rw [← (mem_filter.mp hj).2]; exact hV j
        rw [norm_smul,← mul_assoc]; refine (mul_le_mul_of_nonneg_right hv (norm_nonneg _)).trans (le_trans (b:=w j*‖ν' j‖/(N:ℝ)) (le_of_eq (by ring)) (div_le_div_of_nonneg_right (hp _) hN.le))
      rw [Finset.sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right (show (C.card:ℝ)≤ (N:ℝ) from Nat.cast_le.mpr (hT i)) (div_nonneg hc hN.le)).trans_eq (by field_simp)
    · rw [solo_feed,hook_sales,solo_com v P, Prod.snd_sum,Prod.snd_sum,MergeProof.Float.prof_sum (fun i=>(U i).snd.2) (fun i=>(hU i).normK)]; simp only [Finset.sum_apply]; rw [← sum_add_distrib]; refine sum_congr rfl (fun k _=>?_); unfold U; rw [show (v k • P k).2.2= v k • (P k).2.2 from rfl,profile_scale]; simp only[Pi.smul_apply,smul_eq_mul,←mul_add,hΨ]
    rw [hF,carry_play]; simp only[map_add,solo_mach,map_sum]
    intro i; simp only [Poly.part_plus,mute,Poly.part_sum,show ∀ j,(H j i).part R.quiet=0 from (fun i'=>(hX i').sil i),sum_const_zero,add_zero]
end YM.RG05Readout.Many
