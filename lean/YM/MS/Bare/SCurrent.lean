import YangMills.WilsonProof.NativeSupport.YM.MS.Bare.Spark
/-!
# Analytical λ-field and Cartan nilpotence

This is still finite formal proof on symbols, input gauge group later.
  Keep local flat insertions vetted at all rank. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Bare.Focus
open Function Filter Finset Set Koszul Cylinder Taylor Complex
open scoped Topology ContDiff
variable {A I J K E:Type*}{p:Sector A}{B:Bonded p I}{X:Focus B J K}
variable [Fintype I][Fintype J][Fintype K][NormedAddCommGroup E][NormedSpace ℝ E]
local notation "C"=>X.spark
local notation "μ"=>product p
local notation "R"=>Raw A ℂ
variable (Y: Glow X E) {τ:K→K→K→ℝ} {V:K→E→E}
local notation "L"=> launch Y τ V
local notation "D₀"=> S Y τ V
local notation "P" =>ink Y.e0
local notation "α2"=> (1/2:ℂ)
structure Vibes (τ:K→K→K→ℝ) (V:K→E→E): Prop where
    pole : Metric K τ
    smooth i : germ (V i)
    swaps i j: ∀ᶠ a:E in 𝓝 0, fderiv ℝ (V j) a (V i a) - fderiv ℝ (V i) a (V j a)= ∑ k:K,τ i j k • V k a
namespace Vibes
variable (h:Vibes τ V)
include h
omit [Fintype I] in
lemma vectorSeed (i j): germ (Y.seed i ∘ V j):= (Y.seed i).contDiff.contDiffAt.comp 0 (h.smooth j)
omit [Fintype I] in
lemma antijet (i:J)(k l:K) : P (rotate (V k) (Y.seed i ∘ V l))-P (rotate (V l) (Y.seed i ∘ V k))=∑ j:K,(τ k l j:ℂ) • P (Y.seed i ∘ V j):= by
    let Z m :E→ℝ:= Y.seed i ∘ V m; let W k l:=rotate (V k) (Y.seed i ∘ V l); have hs k l : germ (W k l):= ((h.vectorSeed Y i l).fderiv_right (m:=ω) (by simp)).clm_apply (h.smooth k)
    change P (W k l) - P (W l k)=_; have he : W k l-W l k =ᶠ[𝓝 0] ∑ j:K,τ k l j • Z j:= by
       filter_upwards [(h.swaps k l), (h.smooth k).eventually (by simp),(h.smooth l).eventually (by simp)] with a ha hx hv; simp only [Pi.sub_apply, W,rotate,Z,fderiv_comp a (Y.seed i).differentiableAt (hx.differentiableAt (by simp)),fderiv_comp a (Y.seed i).differentiableAt (hv.differentiableAt (by simp)),(Y.seed i).fderiv,ContinuousLinearMap.comp_apply,← map_sub,ha,map_sum,map_smul, Finset.sum_apply]; rfl
    rw [← ink_sub _ (hs k l) (hs l k), inkit Y.e0 he, ink_sum _ _ (fun j _=> show germ (τ k l j • Z j) from (h.vectorSeed Y i j).const_smul (τ k l j))]; unfold Z; simp_rw [ink_smul _ (h.vectorSeed Y i _)]
lemma stone_s (i:J): D₀ (stone Y V i)=0:= by
   let Rj (k:K):= P (Y.seed i ∘ V k); let T k l := P (rotate (V k) (Y.seed i ∘ V l)); let G a b u:= μ (αc a b X) u
   have h0 k : D₀ (μ (C k) (Rj k))=μ (X.shadow τ k) (Rj k)- ∑ j:K,G k j (T j k):= by
      rw [(show D₀ (μ (C k) _) = μ (D₀ (C k)) (Rj k)+(cross true true:ℂ) • μ (C k) (D₀ (Rj k)) from (lifting Y τ V h.smooth).acts_graded (H:=Rj k) (X.spark_p k))] -- defeq ambiguity
      unfold Rj; rw [chew, cast_ink _ _ _ (h.vectorSeed Y i k) h.smooth,map_sum]; simp only [cross_true,neg_smul,one_smul,← times_assoc]; rfl
   unfold stone; change D₀ (∑ k, μ (C k) (Rj k))=0; rw [map_sum]; simp_rw [h0, Finset.sum_sub_distrib]; rw [sub_eq_zero]
   have hb : ∑ k:K, μ (X.shadow τ k) (Rj k)=∑ k:K,∑ j:K,(-α2) • G k j (T k j-T j k):= by
       simp only [shade_expr,map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply]
       change ∑ k,∑ j,∑ l, (-(1/2:ℂ) * τ j l k) • G j l (Rj k)= _
       rw [← row_three (fun k j l=> (-α2*(τ k j l:ℂ)) • G k j (Rj l))]; refine Finset.sum_congr rfl fun k _=> Finset.sum_congr rfl fun j _=>?_
       rw [show T k j - T j k=∑ l:K,(τ k j l:ℂ) • Rj l from h.antijet Y i k j]; unfold G; simp_rw [map_sum,map_smul, Finset.smul_sum,smul_smul]
   have he : ∑ k:K,∑ j:K,(-α2) • G k j (T k j)= ∑ k:K,∑ j:K,α2 • G k j (T j k) := by
       rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=> Finset.sum_congr rfl fun b _=>?_ ; unfold G; rw [pair_s X b a]; simp
   rw [hb]; simp_rw [show ∀ a b u v,G a b (u-v)=G a b u-G a b v from fun a b _ _=> map_sub ..,smul_sub, Finset.sum_sub_distrib]; rw [he]; simp_rw [neg_smul,← Finset.smul_sum,Finset.sum_neg_distrib]; rw [sub_neg_eq_add]; simp_rw [← Finset.smul_sum]; rw [← add_smul]; norm_num
lemma nilpotent (i:I) : D₀ (L i)=0:= h |> (fun h=> X.pick (fun i=>D₀ (L i)=0) (fun i=>by rw [launch_stone]; exact stone_s Y h i) (fun i=>by rw [launch_shadow]; exact h.pole.stops Y V h.smooth i) i)
end Vibes
end YM.MS.Bare.Focus
