import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Suites
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Real interaction perturbation, single-log Taylor alphabet

One interaction head (`exp(f) - 1`) can contribute at *every* positive
order; rank is the number of insertions of `f`, **not** the number of
heads. Retain through p inclusive. In the RG application the last slot is
charged at p+1 in all truncated product estimates; all derivatives
requested in E6 are included simultaneously. This does not call for Taylor
expansion in the physical coupling of cutoff-dependent coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Series
open Function Filter Finset Metric ConnectedActivityE6.Blaze
open scoped Topology ContDiff BigOperators

/-- At one head: orders 1..p, then the tail. -/
abbrev Letter (p : ℕ) := Fin (p+1)
abbrev rank {p : ℕ} (n : Letter p) := n.val+1

/-- Entire divided differences of exp. -/
def over (i : ℕ) : ℝ → ℝ := (swap dslope 0)^[i] Real.exp

lemma recur (i : ℕ) : over (i+1) = dslope (over i) 0 := by
  unfold over; rw [Function.iterate_succ_apply']

lemma overSeries (i : ℕ) : HasFPowerSeriesAt (over i)
    (FormalMultilinearSeries.fslope^[i] (NormedSpace.expSeries ℝ ℝ)) 0 := by
  apply HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope
  rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.exp_hasFPowerSeriesAt_zero ..

lemma over_at_zero (i : ℕ) : over i 0 = (i.factorial:ℝ)⁻¹ := by
  have h : (FormalMultilinearSeries.fslope^[i] (NormedSpace.expSeries ℝ ℝ)).coeff 0 = over i 0 := (overSeries i).coeff_zero 1
  rw [FormalMultilinearSeries.coeff_iterate_fslope,zero_add] at h
  refine h.symm.trans ?_
  change (NormedSpace.expSeries ℝ ℝ i fun _ => 1)=_
  rw [NormedSpace.expSeries_apply_eq]
  simp

lemma over_smooth (i : ℕ) : ContDiff ℝ ∞ (over i) := by
  induction i with
  | zero => exact Real.contDiff_exp
  | succ i ih =>
    apply contDiff_iff_contDiffAt.mpr; intro x; by_cases hx : x=0
    · subst x; exact (show AnalyticAt ℝ (over _) 0 from ⟨_, overSeries (i+1)⟩).contDiffAt
    rw [recur]; refine (?_ : ContDiffAt ℝ ∞ (slope (over i) 0) x).congr_of_eventuallyEq
      (dslope_eventuallyEq_slope_of_ne _ hx)
    rw [show slope (over i) 0 = (fun z=> (over i z-over i 0)/z) from funext fun z=> by rw [slope_def_field,sub_zero]]
    exact (ih.contDiffAt.sub contDiffAt_const).div contDiffAt_id hx

def mono (i : ℕ) (x : ℝ) : ℝ := x^i / (i.factorial:ℝ)
def tail (i : ℕ) (x : ℝ) : ℝ := x^i * over i x
def split {p : ℕ} (q : Letter p) := if q.val<p then mono (rank q) else tail (rank q)

lemma steps (i : ℕ) (x : ℝ) : tail i x=mono i x+tail (i+1) x := by
  have h := sub_smul_dslope (over i) 0 x
  rw [sub_zero, smul_eq_mul, ← recur, over_at_zero] at h
  unfold tail mono; rw [pow_succ, mul_assoc, h, div_eq_mul_inv]; ring

lemma frame (p : ℕ) (x : ℝ) : tail 1 x=(∑ i ∈ range p, mono (i+1) x)+tail (p+1) x := by
  induction p with
  | zero => simp
  | succ p hi => rw [sum_range_succ,hi, steps (p+1)]; abel

def mellow (x : ℝ) := Real.exp x-1
lemma allLetters (p : ℕ) (x : ℝ) : mellow x=∑ q:Letter p, split q x := by
  rw [show mellow x=tail 1 x from ?_, frame p]
  · rw [Fin.sum_univ_castSucc, ← Fin.sum_univ_eq_sum_range]; congr 1
    · exact Finset.sum_congr rfl fun i _=> by simp [split,rank,i.isLt]
    simp [split,rank]
  have he := steps 0 x; simp only [mono,tail, over, pow_zero,one_mul,Function.iterate_zero_apply,
    Nat.factorial_zero,Nat.cast_one,div_one] at he
  unfold mellow; apply sub_eq_iff_eq_add.mpr; rw [add_comm]; exact he

lemma smooth {p : ℕ} (i : Letter p) : ContDiff ℝ ∞ (split i) := by
  unfold split; split_ifs
  · unfold mono; fun_prop
  unfold tail; exact (contDiff_id.pow _).mul (over_smooth _)

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f:E→ℝ} {j : ℕ} {v d:ℝ} {x:E}

lemma power (h : Brush j v d f x) (i : ℕ) : Brush j (v^i) (d*i) (fun y=> f y^i) x := by
  induction i with
  | zero => simpa using (Brush.certified (k:=j) (x:=x) (le_refl 0) (1:ℝ))
  | succ i hi =>
    simp only [pow_succ,Nat.cast_add,Nat.cast_one, mul_add, mul_one]; exact hi.paints h
end

/-- `v` includes the exponent head bound, through all requested derivatives;
we will use it before multiplying in the Gaussian law scores. -/
lemma allowance (p j:ℕ) : ∃ C:ℝ, 1≤C ∧ ∀ (i:Letter p) (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f:E→ℝ) (x:E) (v d:ℝ), Brush j v d f x → v≤1 → Brush j (C*v^rank i) (d*((p:ℝ)+3)) (split i ∘ f) x := by
  obtain ⟨c,hc,h⟩:= Brush.compact (k:=j) (isCompact_closedBall (0:ℝ) 1)
    (fun _ (_: _∈ closedBall (0:ℝ) 1)=> ((over_smooth (p+1)).of_le (show (↑j:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top)).contDiffAt)
  let C:ℝ := 1+(j.factorial:ℝ)*c; have hC:1≤C:=le_add_of_nonneg_right (by positivity)
  refine ⟨C,hC,?_⟩; intro i E _ _ f x v d hp hv; have hf:= hp.pos; have h0:=hp.nonneg
  let n:= rank i; have hn:(n:ℝ)≤ (p:ℝ)+1 := by exact_mod_cast (show n≤p+1 from Nat.succ_le_succ (by omega))
  unfold split; split_ifs with he; swap
  · have heq:rank i=p+1:=congr_arg Nat.succ (Nat.le_antisymm (by omega) (Nat.le_of_not_gt he))
    rw [heq]; have hh : Brush j c 1 (over (p+1)) (f x) := h _ (mem_closedBall_zero_iff.mpr (hp.bound.trans hv))
    refine ((power hp (p+1)).paints (hp.pine hh)).climb ?_ ?_
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg h0 _)
    push_cast; nlinarith only [mul_le_mul_of_nonneg_right hv hf]
  have hx : ‖((n.factorial:ℝ)⁻¹)‖≤1 := by
    have hy : (1:ℝ)≤(n.factorial:ℝ):=by exact_mod_cast Nat.factorial_pos n
    rw [Real.norm_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ hy
  rw [show mono (rank i) ∘ f=(fun x=> ((n.factorial:ℝ)⁻¹) • (f x^n)) from funext fun x=> by unfold mono; change _/(_ : ℝ)=_*_; ring]
  exact ((power hp n).smul _).climb (mul_le_mul_of_nonneg_right (hx.trans hC) (pow_nonneg h0 _)) (mul_le_mul_of_nonneg_left (by linarith) hf)
end YM.LocalTaylorR2.Series
