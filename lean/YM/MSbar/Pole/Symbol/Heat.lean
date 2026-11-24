import YM.MSbar.Pole.Symbol.View
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Feynman-gauge proper-time covariance derivative
The function here is the scalar part for `r d/dr` of a hard line, not changing
the exponential to a growing function at zero spuriously. Use `H=exp(-r²p²)`.
It is estimated at every positive scale with no excluded external momenta.
-/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set Filter MeasureTheory Ambient
open scoped Topology InnerProductSpace ContDiff BigOperators Classical Interval
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma shrub : Packet (univ:Set E) 1 (ticket (@id E)) (fun x:E=> Real.exp (-(‖x‖^2))) := by
  let G(x:E):=Real.exp (-(‖x‖^2)); let v:= ticket (@id E)
  have hg : ContDiff ℝ ∞ G:=Real.contDiff_exp.comp (contDiff_id.norm_sq ℝ).neg
  have hb' : Bills univ 1 v G := by
    intro k; let f (r:ℝ):= (2*r)^k * Real.exp (-r)
    have hf : Tendsto f atTop (nhds 0):=by simpa only [f,mul_pow,mul_assoc,mul_zero] using ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul ((2:ℝ)^k))
    obtain ⟨N,h⟩:=eventually_atTop.mp (hf.eventually (ge_mem_nhds (
      b:=0) (a:=1) zero_lt_one))
    let K:=max 1 N
    refine ⟨max 1 ((1+K)^k),0,(zero_le_one.trans (le_max_left ..)),fun x _=> ?_⟩
    let r:=‖x‖; have hx:r≥0:= norm_nonneg _
    change ‖Real.exp _‖ * (1+r)^k ≤ _*1^0; rw [pow_zero,mul_one,Real.norm_of_nonneg (Real.exp_pos _).le]
    by_cases ht : K ≤ r
    · have he: 1≤r:=le_trans (le_max_left 1 _) ht
      have hl : -(r^2) ≤ -r:= by nlinarith
      exact (le_trans (mul_le_mul (Real.exp_le_exp.mpr hl) (pow_le_pow_left₀ (by positivity) (show 1+r≤2*r by linarith) _)
        (by positivity) (Real.exp_pos _).le) (Eq.trans_le (mul_comm ..) (h r (le_trans (le_max_right ..) ht)))).trans (le_max_left ..)
    calc
      _ ≤ 1*(1+K)^k:=mul_le_mul (Real.exp_le_one_iff.mpr (by exact neg_nonpos.mpr (sq_nonneg _))) (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) zero_le_one
      _ ≤ _ := by simp
  have hb : Packet univ (1*v) 1 (fun x:E=> -(‖x‖^2)):=Packet.built (Function.HasTemperateGrowth.neg (Function.hasTemperateGrowth_norm_sq E))
    (bill_byprice (fun x _=>le_of_eq (one_mul _).symm))
  let F(x:E):= -(‖x‖^2); let H := fderiv ℝ F
  have hx : fderiv ℝ G=fun x=> G x • H x := by
    ext1 x; exact (((hb.smooth x (mem_univ _)).differentiableAt (by simp)).hasFDerivAt.exp).fderiv
  have hF(j:ℕ):∀ i ≤ j, Bills univ 1 v (iteratedFDeriv ℝ i G):=by
    induction j with
    | zero=> rintro i hi; rw [Nat.le_zero.mp hi]; exact hb'.dominates (by simp)
    | succ j ih=>
      intro i hi; rcases eq_or_lt_of_le hi with hi|hi
      · subst i
        have hu := Packet.spendAt (s:=univ) (g:=H) (fun x _=> (hg.of_le (m:=↑j) (by exact_mod_cast (show (↑j:ℕ∞)≤⊤ from le_top))).contDiffAt)
          ih (fun x h=>hb.fderiv.localn _ h) (fun i _=> hb.fderiv.budget i) (ContinuousLinearMap.lsmul ℝ ℝ)
        refine hu.dominates (fun x _ => ?_); rw [iteratedFDeriv_succ_eq_comp_right,comp_apply,LinearIsometryEquiv.norm_map]
        change ‖iteratedFDeriv ℝ j (fderiv ℝ G) x‖ ≤ _; rw [hx]; exact le_rfl
      exact ih i (by omega)
  exact ⟨fun x _ => hg.contDiffAt, fun i=>hF i i le_rfl⟩

namespace Heat
-- avoid hp dims
variable {n : ℕ}
def wave (r : ℝ) (x : place n) : ℂ:= 2*(r:ℂ)^2*(Real.exp (-(‖r • x‖^2)):ℂ)
lemma cost {r:ℝ} (hr:0<r) : Packet (univ:Set (place n)) 1 (ticket (@id (place n))) (wave r):=by
  let T : place n→L[ℝ]place n:= r • ContinuousLinearMap.id ℝ _
  have hf := comp_affine_bill T 0 (shrub (E:=place n)) (mapsTo_univ _ (Set.univ)) (p:=1) (q:=ticket (@id (place n))) (Bills.const _) ?_
  · simp only [zero_add] at hf
    refine ( (hf.apply (X:=Complex.ofRealCLM)).mul (Packet.const (2*(r:ℂ)^2))).congr (fun x _=>Eventually.of_forall fun i=>?_)
    unfold wave; exact mul_comm ..
  refine bill_single (C:=1+r⁻¹) (l:=1) (by positivity) fun x hx=>?_
  change ‖1+‖x‖‖≤_* (1+‖0+T x‖)^1; rw [Real.norm_of_nonneg (by positivity),zero_add,pow_one]
  change 1+‖x‖ ≤ _* (1+‖r • x‖); rw [norm_smul,Real.norm_of_nonneg hr.le]; field_simp; nlinarith [norm_nonneg x,mul_nonneg (sq_nonneg r) (norm_nonneg x)]
lemma smooth_zero (x:place n) : ContinuousAt (fun r => wave r x) 0:= by unfold wave; fun_prop
@[simp] lemma drops (x:place n): wave 0 x=0:=by simp [wave]
variable (I : Type)
lemma coherent (r : ℝ) : Texture (I:=I) (fun n x=> wave r x.1):=by -- implicit I issue
  constructor
  · intro n J p x; change wave r (J p)=wave r p; unfold wave; rw [← map_smul J,LinearIsometryEquiv.norm_map]
  intro n x i; change wave r _=wave r _; unfold wave; rw [← map_smul (place.pad n) r x,place.pad_at,place.squared]; simp
end Heat
end YM.MSbar.Pole
