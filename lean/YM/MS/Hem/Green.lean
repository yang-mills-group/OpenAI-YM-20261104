import YM.MS.Hem.Excise
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
/-!
# Pedestals (summation estimates for all log lengths to the IR test anchor)

Mellin integrand decay assessed after flat momenta Taylor projections. z bus.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Hem.Mell
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine
open scoped Topology ContDiff
variable {I:Type}{G:Gauge}{j m n k:ℕ}{x:ℂ}{R:ℝ}{F H:Mob G}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
open YM.MS.Alps.Bench.Forest
variable {u:I→ℂ}{v:I→ℝ}{a:ℝ}{f:I→ E→ℂ}
local notation "S" => Arc.path (0:Arc.UScale I)
variable (h:veg 0 f 1)(hp:∀ i, (v i)≤0)(hu:∀ i,a≤(u i).re+k)
include h hp hu
omit h hp hu in
lemma amount_norm (t:ℝ)(q:ℂ): ‖amount q t‖=Real.exp (q.re*t):= by simp [amount, Complex.norm_exp, mul_comm]
-- omit section vars
lemma tall (j:ℕ)(hk:k≤j) : (S).full.Part S (fun i=> Alps.Bench.Forest.patch (f i) (u i) (v i)) (fun i _=> Real.exp (a*v i)) j := by
   obtain ⟨C,hC,b,hb⟩:= ride h j; refine ⟨C,hC,b,fun i p _=>?_⟩; let q:= v i; let G:=f i; let g := u i; let D := Real.exp q; have Hx : ContDiff ℝ j G := (h.smooth i).of_le (by exact_mod_cast le_top); specialize hu i;
   have ht: ContDiff ℝ j (fun p=> G (D • p)):= Hx.comp (by fun_prop : ContDiff ℝ _ fun p:E=>D • p)
   have Hz : 0<D := exp_pos _; have hv : D ≤ 1:= exp_le_one_iff.mpr (hp i)
   change ‖iteratedFDeriv ℝ j (amount g q • fun x:E=> G (D • x)) p‖ ≤ C*(S).full.cheap i p^b*(exp (a*q)* (S).length i^j)
   rw [iteratedFDeriv_const_smul_apply ht.contDiffAt,iteratedFDeriv_comp_const_smul D Hx,norm_smul,norm_smul,norm_of_nonneg (pow_nonneg Hz.le _)]; rw [amount_norm]; rw [g_cost,cheap_length,Pi.zero_apply,abs_zero,add_zero,one_mul,one_pow,mul_one, ← mul_assoc]
   have hm : exp (g.re*q)*D^j ≤ exp (a*q):= by
       unfold D; rw [← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_le_exp.mpr;
       rw [← add_mul]; have hx: (k:ℝ) ≤ j:= by exact_mod_cast hk
       exact mul_le_mul_of_nonpos_right (by unfold g; linarith) (hp i)
   rw [mul_comm _ (exp (a*q))]; apply mul_le_mul hm _ (norm_nonneg _) (exp_pos _).le; refine (hb i (D • p)).trans ?_; simp only [Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,one_mul,mul_one]; rw [norm_smul,norm_of_nonneg Hz.le]; gcongr; exact mul_le_of_le_one_left (norm_nonneg _) hv
lemma fade (hv:∀ i j,j<k → iteratedFDeriv ℝ j (f i) 0=0): veg 0 (fun i=> Alps.Bench.Forest.patch (f i) (u i) (v i)) (fun i=> exp (a*v i)):= by
   have ht (i:I): ContDiff ℝ ∞ (Alps.Bench.Forest.patch (f i) (u i) (v i)):= (patch_w (h.smooth i) (u i)).comp (( contDiff_const.prodMk contDiff_id): ContDiff ℝ ∞ fun x:E=> (v i,x))
   refine ⟨ht,fun j=>?_⟩; by_cases hx : k ≤ j; exact tall h hp hu j hx
   have H : j ≤ k:= Nat.le_of_lt (lt_of_not_ge hx); clear hx; induction H using Nat.decreasingInduction with
   | self => exact tall h hp hu k le_rfl
   | of_succ i hi ih=>
       refine LogTime.lower_jet S ht (Cost.of_le (fun j p hp=>?_)) ih; let V:= (f j); let A:= exp (v j); have hm:ContDiff ℝ i V:= (h.smooth j).of_le (by exact_mod_cast le_top); change ‖iteratedFDeriv ℝ i (amount (u j) (v j) • fun x=> V (A • x)) 0‖ ≤ exp (a*v j)* (S).length j^i; rw [iteratedFDeriv_const_smul_apply (ContDiff.contDiffAt (f:=fun x=>V (A • x)) (hm.comp (g:=V) (f:=fun x:E=>A • x) (by fun_prop))),iteratedFDeriv_comp_const_smul _ hm]; simp only [V,hv j i hi,smul_zero,norm_zero,cheap_length,one_pow,mul_one]; positivity
end YM.MS.Hem.Mell
