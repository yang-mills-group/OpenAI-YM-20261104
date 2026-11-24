import YM.OPE.Compatible.Tune.Arco
import YM.OPE.Compatible.Spa.Tempo
/-!
# Finite suspension.P. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Set Filter
open Drift
open scoped Topology BigOperators Classical
variable {M:Type}{d k:ℕ}{r p μ:ℝ}{V:ℕ→ ΦB (Dryst d)}{T:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d)}
open scoped RealInnerProductSpace
local notation "J!"=> Dryst d
local notation "W!"=> Jewel (Dryst d)
local notation "τ!"=>τΓ (Dryst d)
local notation "U!"=>τ₀ (Dryst d)
section
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
noncomputable def Filmμ (r:ℝ): Jewel E→ₗ[ℝ] E:= LinearMap.proj 0+r • (LinearMap.proj 1)+(r^2) • (LinearMap.proj 2)
lemma film_eq (x:Jewel E):Filmμ r x=x 0+r • x 1+(r^2) • x 2:=rfl
noncomputable def κeval (r:ℝ)(T:Jewel E→ₗ[ℝ] Jewel E): E→ₗ[ℝ] E:= (Filmμ r).comp (T.comp (τ₀ E))
end
lemma accounts (x:W!) : ‖(Filmμ r x)‖^2 = ‖x 0‖^2 + (2*inner ℝ (x 0) (x 1))*r+ (2*inner ℝ (x 0) (x 2)+‖x 1‖^2)*r^2 + r^3*(2*inner ℝ (x 1) (x 2)+ r*‖x 2‖^2):=by
       rw [film_eq]; simp_rw [← real_inner_self_eq_norm_sq, inner_add_left,inner_add_right, real_inner_smul_left,real_inner_smul_right]; rw[real_inner_comm (x 2) (x 0), real_inner_comm (x 1) (x 0),real_inner_comm (x 2) (x 1)]; ring
variable (H:Auth V T μ)
variable {Y:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d)}(Q:Clamp k μ Y V)
include H Q
lemma Clamp.plume (x:Dryst d)(ht:0 < μ):
    let q:=Y (τ₀ (Dryst d) x); ‖κeval r Y x‖^2= (μ^k*‖x‖)^2+ ((k:ℝ)*(μ^k)^2*SurTax T V μ x x)*r^2 +r^3 * (2*inner ℝ (q 1) (q 2)+r*‖q 2‖^2):=by
       intro q; change ‖Filmμ r q‖^2= _; have hz:=Q.x0 x; rw[accounts,show q 0=(μ^k)•x from hz, show inner ℝ _ (q 1)=0 from Q.crispAct H x, show 2*inner ℝ _ (q 2)+_= _ from Q.bold H x ht,norm_smul,Real.norm_of_nonneg (pow_pos ht _|>.le)]; ring
omit Q H
-- CLM currency
lemma Fiscal (A: Artπ (Dryst d)):∃ C:ℝ,0≤C ∧∀ x:Dryst d,|A x x|≤C*‖x‖^2:=by
       let F: J!→ₗ[ℝ] J!→L[ℝ] ℝ := (LinearMap.toContinuousLinearMap).toLinearMap.comp A; let C:=F.toContinuousLinearMap; refine ⟨‖C‖,ContinuousLinearMap.opNorm_nonneg C,fun x=>?_⟩; apply ((show ‖C x x‖≤‖C x‖*‖x‖ from (C x).le_opNorm x).trans (mul_le_mul_of_nonneg_right (C.le_opNorm x) (norm_nonneg _))).trans_eq; ring
abbrev ζCost (T:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d)):ℝ:= ‖T.toContinuousLinearMap‖*‖(τ₀ (Dryst d)).toContinuousLinearMap‖
lemma AmpQ (x:Dryst d)(j:Fin 3) (U:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d)) :‖U (τ₀ (Dryst d) x) j‖ ≤ ζCost U*‖x‖:=by
       unfold ζCost; rw [mul_assoc]; exact (norm_le_pi_norm _ j).trans ((U.toContinuousLinearMap.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((τ₀ (Dryst d)).toContinuousLinearMap.le_opNorm x) (norm_nonneg _)))
lemma BoundPv (x:Dryst d)(U:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d))(h:|r|≤1):
     let q:= U (τ₀ (Dryst d) x); |(2*inner ℝ (q 1) (q 2)+r*‖q 2‖^2)|≤3 * ζCost U ^2* ‖x‖^2:=by
       intro q; apply (abs_add_le ..).trans; simp only [abs_mul, abs_norm, abs_pow, abs_two]; let v:= ζCost U*‖x‖; have ht: ‖q 2‖ ≤v:=AmpQ x 2 U; have hp: |inner ℝ (q 1) (q 2)| ≤v*v:= (abs_real_inner_le_norm ..).trans (mul_le_mul (AmpQ x 1 U) ht (norm_nonneg _) ((norm_nonneg _).trans (AmpQ x 1 U))); have hv: |r| *‖q 2‖^2 ≤ v*v:=by rw [pow_two];exact (mul_le_mul h (mul_self_le_mul_self (norm_nonneg _) ht) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (one_mul _) -- lhs pow
       apply le_trans (add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) hv); dsimp only[v]; exact le_of_eq (by ring)
include H
lemma soar: ∃ C:ℝ, 1 ≤ C∧∀ k (Y:Jewel (Dryst d)→ₗ[ℝ] Jewel (Dryst d)), Clamp k μ Y V →∀ x:Dryst d,∀ r:ℝ,|r|≤1→0<μ→ |‖κeval r Y x‖^2 - (μ^k*‖x‖)^2|≤ ((k:ℝ)*(μ^k)^2*C*r^2+|r|^3*3*ζCost Y^2)*‖x‖^2:= by
       obtain ⟨c,hc,h⟩:= Fiscal (SurTax T V μ); refine ⟨1+c,(by linarith),fun k Y Q x r hr ht=>?_⟩; let v:= Y (τ₀ (Dryst d) x); rw [Clamp.plume H Q _ ht,add_assoc, add_sub_cancel_left]; apply (abs_add_le ..).trans; rw [abs_mul,abs_mul (↑k * ((μ ^ k)^2)) (SurTax T V μ x x), abs_of_nonneg (mul_nonneg (by positivity) (by positivity)),abs_of_nonneg (sq_nonneg r),abs_mul  (r^3) _,abs_pow]; refine (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_trans (h x) (mul_le_mul_of_nonneg_right (show c≤1+c by linarith) (sq_nonneg _))) (by positivity)) (sq_nonneg r)) (mul_le_mul_of_nonneg_left (BoundPv x Y hr) (by positivity))).trans_eq ?_; ring
end YM.OPE.Hark
