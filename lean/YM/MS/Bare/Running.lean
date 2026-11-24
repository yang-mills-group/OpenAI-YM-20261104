import YM.MS.Bare.SCurrent

/-!
# Bare master and Haar payee

Still finite alphabet. Individual rank parts assembled later.
 Trace term is from spin, gauge trace included (uses unimodularity).
-/
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

-- ghost trace (left). antisym yields T(c0,b). Prove coordinate.
namespace Metric
variable (X) (h:Metric K τ)
include h
omit [Fintype I] [Fintype J] in
lemma cascades (i j:K) : D (B.plain (X.KId i)) (X.shadow τ j)=∑ k:K, (-(τ i k j:ℂ)) • (X.spark k) := by
    classical
    have ht (f:Raw A ℂ) : μ f (coin 1)= f:= by rw [← (coin_pure _).central,coin_product,one_smul]
    have he (v:K) : D (B.plain (X.KId i)) (C v)= if v=i then coin 1 else 0:= by
       split
       next h=> exact h ▸ X.spark_me _
       next h=> exact X.spark_far v (Ne.symm h)
    simp_rw [shade_expr,map_sum,map_smul,D_product,(X.spark_p _).signs,show p (B.plain (X.KId i))=true from X.gauge i,LinearMap.map_smul_of_tower,LinearMap.smul_apply, smul_add, Finset.sum_add_distrib,he]; -- check lint
    let f u:ℂ := τ i u j;
    rw [Finset.sum_eq_single i]; swap
    · intro b hb hi; simp [hi]
    swap
    · simp
    simp only [if_true,coin_product,one_smul,apply_ite,ht,map_zero,smul_zero]; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun k _=>?_); rw [Fintype.sum_ite_eq',smul_smul,← add_smul,h.skew k i j]; congr 1; push_cast; rw [cross_true]; ring
omit [Fintype I][Fintype J] in
lemma casc_end : (∑ i:K, D (B.plain (X.KId i)) (X.shadow τ i))=0:= by
    simp_rw [h.cascades X]; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul, Finset.sum_neg_distrib,← Complex.ofReal_sum,h.trace]; simp
end Metric

/-! Density invariant state on test F. -/
abbrev Inert (V:K→E→ E)(f:E→ℝ):=∀ i, rotate (V i) f =ᶠ[𝓝 0] 0
def index_div (Y:Glow X E)(V:E→E): E→ℝ:= ∑ j:J, layer (Y.e0 (B.plain (X.AId j))) (Y.seed j ∘ V)
abbrev Sourced (f:E→ℝ) (τ:K→K→K→ℝ) (V:K→E→E)(Y:Glow X E):= ink Y.e0 f+B.hung (launch Y τ V)
def Bills (Y:Glow X E)(V:K→E→E)(f:E→ℝ):=∀ k,index_div Y (V k)+rotate (V k) f=ᶠ[𝓝 0] 0

namespace Vibes
variable {f g:E→ℝ}
variable (h:Vibes τ V)
include h
lemma onto (he:germ g): link B.BV true p (Sourced f τ V Y) (P g)= ∑ k:K, μ (C k) (P (rotate (V k) g)) := by
    rw [Sourced,(lifting Y τ V h.smooth).unstar]; exact cast_ink _ _ _ he h.smooth
    · exact ink_p Y.e0 Y.never _
    all_goals intro i; exact ink_off Y.e0 (Y.dual_off i) _
lemma classicalGauge (he:germ f)(hv:Inert V f): link B.BV true p (Sourced f τ V Y) (Sourced f τ V Y)=0:= by
    refine (lifting Y τ V h.smooth).inv_cl (ink_p _ Y.never _) (fun i=> ink_off _ (Y.dual_off i) _) ?_ (fun i=>h.nilpotent Y i)
    rw [← show S Y τ V=B.glory L from rfl, cast_ink Y τ V he h.smooth]; simp_rw [inkit _ (hv _),ink_zero,map_zero,Finset.sum_const_zero]
omit [Fintype I] in
lemma jeans (k:K): germ (index_div Y (V k)):= by
    let H i := h.vectorSeed Y i k; let G i := layer (Y.e0 (B.plain (X.AId i))) (Y.seed i ∘ V k); unfold index_div; rw [show (∑ i:J,G i)=fun x=>∑ i:J,G i x from funext fun x=> Finset.sum_apply ..]; exact ContDiffAt.sum fun i _=> germ_layer (H i) _

lemma focal_lap : B.BV (Sourced f τ V Y)=∑ k:K,μ (C k) (P (index_div Y (V k))):= by
    rw [Sourced,map_add,B.flat_zero (fun i=> ink_off _ (Y.dual_off i) _),zero_add,(lifting Y τ V h.smooth).force_lap,X.split_i]; simp_rw [launch_stone,launch_shadow,h.pole.casc_end X,add_zero]
    simp_rw [stone,map_sum,D_product,spark_never, show ∀ i,p (B.plain (X.AId i))=false from X.act,sign_id,map_zero,LinearMap.zero_apply,zero_add]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun k _=>?_); unfold index_div; rw [ink_sum _ _ (fun i _=>show germ (layer _ (Y.seed _∘ V _)) from germ_layer (h.vectorSeed Y i k) _),map_sum]; rfl
lemma quantum_pay (he:germ g)(hv:Bills Y V g): B.BV (Sourced f τ V Y)+link B.BV true p (Sourced f τ V Y) (P g)=0 := by
    rw [h.onto Y he, h.focal_lap,← Finset.sum_add_distrib]; apply Finset.sum_eq_zero; intro k _; rw [← map_add, ← ink_add _ (h.jeans Y k) (show germ (rotate (V k) g) from (he.fderiv_right (m:=ω) (by simp)).clm_apply (h.smooth k)), inkit _ (hv k), ink_zero,map_zero]
end Vibes
omit [Fintype K] in
lemma lap_g (f:E→ℝ): B.BV (P f)=0:= B.flat_zero fun i=> ink_off _ (Y.dual_off i) _
omit [Fintype K] in
lemma link_g (f g:E→ℝ): link B.BV true p (P f) (P g)=0:= by simp only [B.by_lap (ink_p _ Y.never _),ink_off _ (Y.dual_off _),map_zero,LinearMap.zero_apply,zero_add,smul_zero,Finset.sum_const_zero]
end YM.MS.Bare.Focus
