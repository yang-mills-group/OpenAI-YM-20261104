import YM.Integration.FVA1Physical.Exchange.EvenTaylorLaw
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The exact two-state Gibbs reading computed from separately specified
weights. A common forced energy or arbitrary positive relative proposal
can be retained, independently of its size. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.FVA1Physical.FibreMeasure
open Set
def gibbsOdds (t : ℝ) := Real.exp t/(1+Real.exp t)

theorem normalized_odds {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    gibbsOdds (Real.log a-Real.log b) = a/(a+b) := by
  rw [gibbsOdds,Real.exp_sub,Real.exp_log ha,Real.exp_log hb]
  field_simp
  ring

private theorem odds_derivative (t : ℝ) :
    HasDerivAt gibbsOdds (Real.exp t/(1+Real.exp t)^2) t := by
  have n : 1+Real.exp t≠0 := by positivity
  have d := (Real.hasDerivAt_exp t).div ((Real.hasDerivAt_exp t).const_add 1) n
  apply d.congr_deriv
  change (Real.exp t*(1+Real.exp t)-Real.exp t*Real.exp t)/(1+Real.exp t)^2 = _
  ring

theorem odds_lipschitz (a b : ℝ) : |gibbsOdds a-gibbsOdds b| ≤ |a-b|/4 := by
  have bound (t : ℝ) : ‖deriv gibbsOdds t‖≤1/4 := by
    rw [(odds_derivative t).deriv,Real.norm_of_nonneg (by positivity)]
    apply (div_le_div_iff₀ (sq_pos_of_pos (show 0<1+Real.exp t by positivity)) (by norm_num)).mpr
    nlinarith [sq_nonneg (Real.exp t-1)]
  have L := (convex_univ (𝕜:=ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f:=gibbsOdds) (fun t _ => (odds_derivative t).differentiableAt)
    (fun t _ => bound t) (mem_univ b) (mem_univ a)
  simpa only [Real.norm_eq_abs,div_mul_eq_mul_div,one_mul] using L

/-- The first law uses the original two positive weights. The second uses
the retained gas odds and an independently issued regular action increment.
Both tests are chosen independently and may be complex or vector-valued. -/
theorem paid_gibbs_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (ha : 0<a) (hb : 0<b) (forced issued : ℝ) (F H : E)
    (f : ‖F‖≤1) (h : ‖H‖≤1) :
    let q := a/(a+b)
    let p := gibbsOdds (forced+issued)
    ‖(q • F+(1-q) • H)-(p • F+(1-p) • H)‖ ≤
      |(Real.log a-Real.log b-forced)-issued|/2 := by
  intro q p
  have eqn : q • F+(1-q) • H-(p • F+(1-p) • H)=(q-p) • (F-H) := by
    simp only [sub_smul,one_smul,smul_sub];abel
  rw [eqn,norm_smul,Real.norm_eq_abs]
  have pm : |q-p|≤|(Real.log a-Real.log b-forced)-issued|/4 := by
    dsimp only [q,p]
    rw [←normalized_odds ha hb,sub_sub]
    exact odds_lipschitz .. 
  have len : ‖F-H‖≤2 := (norm_sub_le ..).trans (by linarith)
  exact (mul_le_mul pm len (norm_nonneg _) (by positivity)).trans_eq (by ring)

end YM.Integration.FVA1Physical.FibreMeasure
