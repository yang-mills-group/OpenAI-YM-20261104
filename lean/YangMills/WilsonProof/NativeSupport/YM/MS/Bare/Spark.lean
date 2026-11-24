import YM.MS.Bare.Spark
import YM.MS.Bare.Focus

/-!
# Lie bracket tensor at sites; alternating traces and true focal action

Manually with shuffle graded signs. No relative gauge quotient assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Bare.Focus
open Function Filter Finset Set Koszul Cylinder Taylor
open scoped Topology ContDiff
variable {A I J K E:Type*}{p:Sector A}{B:Bonded p I}{X:Focus B J K}
variable [Fintype I][Fintype J][Fintype K][NormedAddCommGroup E][NormedSpace ℝ E]
local notation "C"=>X.spark
local notation "μ"=>product p
local notation "R"=>Raw A ℂ
variable (Y: Glow X E) (τ:K→K→K→ℝ) (V:K→E→E)
local notation "L"=> launch Y τ V
local notation "D₀"=> S Y τ V
lemma casts (i:I) : D₀ (atLetter (B.plain i))=L i := by
    classical
    rw [Bonded.reveals, Finset.sum_eq_single i,hear,← (coin_pure _).central,coin_product,one_smul]; swap; exact fun h=> (h (Finset.mem_univ _)).elim
    intro j hj hi; rw [unheard _ (fun he=>hi (B.plain.injective he)),map_zero]
lemma chew (v:K): D₀ (C v)=X.shadow τ v:= (casts Y τ V _).trans (launch_shadow ..)

omit [Fintype I][Fintype J] in
lemma shadow_h (X : Focus B J K)(i:K): Pure p false (X.shadow τ i):= Pure.sum _ fun i _=> Pure.sum _ fun j _=> (Pure.prod (X.spark_p i) (X.spark_p j)).smul _
-- work after simp casts
local notation "w2" => (-(1/2):ℂ)
variable (X) in
omit [Fintype I][Fintype J] in
lemma shade_expr (i:K): X.shadow τ i=∑ a:K,∑ b:K,(w2*τ a b i) • product p (X.spark a) (X.spark b):= by unfold shadow; congr! 3; ring
-- triple_C alternate. Jacobi.
def αc (a b:K) (X:Focus B J K): R:=product p (X.spark a) (X.spark b)
def ωc (a b c:K)(X:Focus B J K): R:=product p (αc a b X) (X.spark c)
variable (X) in
omit [Fintype I][Fintype J][Fintype K] in
lemma pair_s (a b:K): αc a b X= -αc b a X:= by simpa [αc] using (X.spark_p a).times_comm (X.spark_p b)
variable (X) in
omit [Fintype I][Fintype J][Fintype K] in
lemma rotates (a b c:K): ωc a b c X=ωc b c a X:= by unfold ωc αc; rw [times_assoc]; exact ((Pure.prod (X.spark_p b) (X.spark_p c)).central _).symm
omit [Fintype I][Fintype J] in
lemma row_three (f:K→K→K→R): ∑ i:K,∑ j:K,∑ k:K,f i j k= ∑ i:K,∑ j:K,∑ k:K,f j k i := by
   conv_rhs=> rw [Finset.sum_comm]
   exact Finset.sum_congr rfl fun i _=> Finset.sum_comm
omit [Fintype I][Fintype J] in
lemma four_turn (f:K→K→K→K→R) : ∑ w:K,∑ c:K,∑ a:K,∑ b:K, f a b c w=∑ a:K,∑ b:K,∑ c:K,∑ w:K, f a b c w:= by
   rw [Finset.sum_comm] -- c w a b
   conv_lhs => arg 2; intro c; rw [← row_three (fun a b w=> f a b c w)] -- should match? want w,a,b to a,b,w. rotate a,b,w → b,w,a? lhs shape in w/a/b = f a b c w = F a b w)
   exact Eq.symm (row_three (fun a b c=> ∑ w:K,f a b c w))
variable {τ}
namespace Metric
variable (h:Metric K τ)
include h
omit [Fintype I][Fintype J] in
lemma lemmaVAC (X:Focus B J K)(i:K): (∑ a:K,∑ b:K,(τ a b i:ℂ) • product p (X.shadow τ a) (X.spark b))=0:= by
    let M a b c w: R:=(w2*(τ a b w*τ w c i:ℝ)) • ωc a b c X; let W:=∑ a:K,∑ b:K,∑ c:K,∑ w:K, M a b c w
    have he : (∑ a:K,∑ b:K,(τ a b i:ℂ) • product p (X.shadow τ a) (X.spark b))= W:= by
       simp only [shade_expr,map_sum,LinearMap.sum_apply, map_smul,LinearMap.smul_apply,Finset.smul_sum,smul_smul]; unfold W
       -- ∑ w c a b -> ∑ a b c w; convert reorder
       rw [← four_turn M]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> Finset.sum_congr rfl fun l _=>?_ ; unfold M ωc αc; congr 1; push_cast; ring
    rw [he]
    let s := M -- ℂ distributed. prove 3W=0
    have h1 : W=∑ a:K,∑ b:K,∑ c:K,∑ w:K, M b c a w:= row_three (fun a b c=>∑ w:K,M a b c w)
    have h2 : W=∑ a:K,∑ b:K,∑ c:K,∑ w:K, M c a b w:= h1.trans (row_three (fun a b c=>∑ w:K,M b c a w))
    have hm : (3:ℕ) • W =0:= by
       rw [show (3:ℕ)•W=W+W+W by abel]
       conv_lhs => lhs; rhs; rw [h1]
       conv_lhs=> rhs; rw [h2]
       unfold W; simp_rw [← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro a _; apply Finset.sum_eq_zero; intro b _; apply Finset.sum_eq_zero; intro c _
       unfold M; simp_rw [rotates X c a b,← rotates X a b c,← add_smul, ← mul_add,← Finset.sum_smul, ← Finset.mul_sum, ← Complex.ofReal_add, ← Complex.ofReal_sum, Metric.acts h a b c i]; simp
    funext x; exact (nsmul_eq_zero_iff_right (by decide : (3:ℕ)≠0)).mp (congr_fun hm x)

lemma stops (hv:∀ i,germ (V i))(i:K): S Y τ V (X.shadow τ i)=0:= by
    let YS a b:=μ (X.shadow τ a) (C b); let T a b:=τ a b i; let L0:=S Y τ V
    have he a b: L0 (μ (C a) (C b))= YS a b - YS b a:= by
        rw [show L0 (μ (C a) (C b))=μ (D₀ (C a)) (C b)+(cross true true:ℂ) • μ (C a) (D₀ (C b)) from (lifting Y τ V hv).acts_graded (H:=C b) (X.spark_p a)]; unfold YS; rw [chew,chew, (shadow_h τ X b).central]; simp [sub_eq_add_neg]

    rw [shade_expr]; change L0 _=_
    simp_rw [map_sum,map_smul,he, smul_sub,Finset.sum_sub_distrib]; rw [sub_eq_zero]
    have h0 i := h.lemmaVAC X i
    have H : ∑ a,∑ b,(w2*τ a b i) • YS a b=w2 • ∑ a,∑ b,(τ a b i:ℂ) • YS a b:= by simp_rw [Finset.smul_sum,smul_smul]
    conv_rhs => rw [Finset.sum_comm]
    rw [show ∑ b:K,∑ a:K,(w2*(τ a b i:ℂ)) • YS b a= -(∑ a:K,∑ b:K,(w2*(τ a b i:ℂ)) • YS a b) by
       simp_rw [← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; nth_rw 1 [h.skew]; simp]
    rw [H]; dsimp only [YS]; rw [h0 i,smul_zero,neg_zero]
end Metric
end YM.MS.Bare.Focus
