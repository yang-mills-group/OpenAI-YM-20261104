import YM.Integration.WilsonOrdinaryPivotFrame

/-! A single positive-coupling smooth realization of a prescribed matrix
jet, before truncation. One real cutoff is applied to each *whole* matrix;
this preserves linear constraints on all of its entries. -/
noncomputable section
namespace YM.Integration.WilsonOrdinaryPivotAsymptotic
open Filter Finset Set Real
open scoped Topology BigOperators Classical ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℕ→E)

private def width (n : ℕ) : ℝ := 2^(n+1)*(1+‖a n‖)+(n:ℝ)+1

omit [NormedSpace ℝ E] in
private theorem large (n : ℕ) : (n:ℝ)<width a n := by
  have p : 0≤(2:ℝ)^(n+1)*(1+‖a n‖) := by positivity
  unfold width;linarith

private def piece (n : ℕ) (t : ℝ) : E :=
  (Real.smoothTransition (2-width a n*t) * t^n) • a n

/-- A single function independent of the subsequent perturbative order. -/
def realizer (t : ℝ) : E := ∑' n : ℕ,piece a n t
def truncation (q : ℕ) (t : ℝ) : E := ∑ n∈range (q+1),t^n • a n

private theorem off (n : ℕ) {t : ℝ} (ht : 2≤width a n*t) : piece a n t=0 := by
  simp only [piece,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr ht),zero_mul,zero_smul]

private theorem fixed (n : ℕ) {t : ℝ} (ht : width a n*t≤1) : piece a n t=t^n • a n := by
  simp only [piece,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-width a n*t),one_mul]

private theorem finite {t : ℝ} (pos : 0<t) :
    ∃ N : ℕ,∀ y : ℝ,t/2<y→∀ n : ℕ,N≤n→piece a n y=0 := by
  obtain ⟨N,hn⟩ := exists_nat_ge (4/t)
  refine ⟨N,fun y hy n hm=>off a n ?_⟩
  have base : 4/t≤width a n := hn.trans ((by exact_mod_cast hm : (N:ℝ)≤n).trans (large a n).le)
  calc
    (2:ℝ) = (4/t)*(t/2) := by field_simp;norm_num
    _ ≤ _ := mul_le_mul base hy.le (by linarith) ((by positivity : (0:ℝ)≤n).trans (large a n).le)

theorem smooth : ContDiffOn ℝ ∞ (realizer a) (Set.Ioi 0) := by
  intro t pos
  obtain ⟨N,cut⟩ := finite a pos
  have eq : realizer a =ᶠ[𝓝 t] fun y=>∑ n∈range N,piece a n y := by
    filter_upwards [lt_mem_nhds (half_lt_self pos)] with y hy
    exact tsum_eq_sum fun n hn=>cut y hy n (Nat.le_of_not_gt fun small=>hn (mem_range.mpr small))
  have good (n : ℕ) : ContDiff ℝ ∞ (piece a n) := by
    have meter : ContDiff ℝ ∞ (fun t : ℝ=>Real.smoothTransition (2-width a n*t)) :=
      Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
    exact (meter.mul (contDiff_id.pow n)).smul contDiff_const
  have finite_sum : ContDiff ℝ ∞ (fun y=>∑ n∈range N,piece a n y) := ContDiff.sum fun n _=>good n
  exact (finite_sum.contDiffAt.congr_of_eventuallyEq eq).contDiffWithinAt

private theorem absolute (n : ℕ) {t : ℝ} (pos : 0≤t) : ‖piece a n t‖≤ t^n * ‖a n‖ := by
  rw [piece,norm_smul,Real.norm_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (pow_nonneg pos _)),mul_assoc]
  exact mul_le_of_le_one_left (mul_nonneg (pow_nonneg pos _) (norm_nonneg _)) (Real.smoothTransition.le_one _)

omit [NormedSpace ℝ E] in
private theorem affordable (n : ℕ) {t : ℝ} (pos : 0<t) (active : width a n*t<2) :
    t*‖a n‖≤(1/2:ℝ)^n := by
  rw [one_div_pow]
  apply (le_div_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) n)).mpr
  have paid : ((2:ℝ)^(n+1)*(1+‖a n‖))*t ≤ width a n*t :=
    mul_le_mul_of_nonneg_right (by unfold width;linarith only [show (0:ℝ)≤n by positivity]) pos.le
  calc
    _ ≤ t*(1+‖a n‖)*2^n := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) pos.le) (by positivity)
    _ = (2^(n+1)*(1+‖a n‖)*t)/2 := by rw [pow_succ];ring
    _ ≤ 1 := by linarith

private theorem tail_bound (q n : ℕ) (large_n : q+2≤n) {t : ℝ} (pos : 0<t) (tiny : t≤1) :
    ‖piece a n t‖≤t^(q+1)*(1/2:ℝ)^n := by
  by_cases hidden : 2≤width a n*t
  · rw [off a n hidden,norm_zero];positivity
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    calc
      _ ≤ _ := absolute a (j+1) pos.le
      _ = t^j * (t * ‖a (j+1)‖) := by rw [pow_succ];ring
      _ ≤ _ := mul_le_mul (pow_le_pow_of_le_one pos.le tiny (by omega : q+1≤j))
        (affordable a _ pos (lt_of_not_ge hidden)) (mul_nonneg pos.le (norm_nonneg _)) (pow_nonneg pos.le _)

private theorem geometric (N : ℕ) : (∑ j∈range N,(1/2:ℝ)^j) ≤ 2 := by
  have eq (N : ℕ) : (∑ j∈range N,(1/2:ℝ)^j) = 2*(1-(1/2:ℝ)^N) := by
    induction N with
    | zero=>simp
    | succ N ih=>rw [sum_range_succ,ih,pow_succ];ring
  rw [eq]
  linarith only [pow_nonneg (by norm_num : (0:ℝ)≤1/2) N]

/-- Every prescribed coefficient, including its sign, of this ONE function.
The scale is chosen before the comparison order. -/
theorem expansion (q : ℕ) :
    ∀ᶠ t in 𝓝[>] (0:ℝ),‖realizer a t - truncation a q t‖ ≤ (‖a (q+1)‖+2)*t^(q+1) := by
  have buy (n : Fin (q+1)) : ∀ᶠ t in 𝓝[>] (0:ℝ),piece a n t=t^n.val • a n := by
    have positive : 0<width a n := (by positivity : (0:ℝ)≤n.val).trans_lt (large a n)
    filter_upwards [(gt_mem_nhds (one_div_pos.mpr positive)).filter_mono nhdsWithin_le_nhds] with t ht
    apply fixed
    have h := (lt_div_iff₀ positive).mp ht
    linarith only [show width a n*t < 1 by simpa only [mul_comm] using h]
  have pos : ∀ᶠ t : ℝ in 𝓝[>] 0,0<t := self_mem_nhdsWithin
  filter_upwards [Filter.eventually_all.mpr buy,pos,(gt_mem_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t head ht ht₁
  obtain ⟨N,cut⟩ := finite a ht
  have total : realizer a t = ∑ n∈range (q+2+N),piece a n t :=
    tsum_eq_sum fun n hn=>cut t (half_lt_self ht) n (by have := not_lt.mp (fun small=>hn (mem_range.mpr small));omega)
  have front : (∑ n∈range (q+1),piece a n t)=truncation a q t :=
    sum_congr rfl (fun n hn=>head ⟨n,mem_range.mp hn⟩)
  have difference : realizer a t - truncation a q t = piece a (q+1) t + ∑ n∈range N,piece a (q+2+n) t := by
    rw [total,Finset.sum_range_add,Finset.sum_range_succ,front]
    abel
  have rest : ‖∑ n∈range N,piece a (q+2+n) t‖ ≤ t^(q+1)*2 := by
    calc
      _ ≤ ∑ n∈range N,‖piece a (q+2+n) t‖ := norm_sum_le _ _
      _ ≤ ∑ n∈range N,t^(q+1)*(1/2:ℝ)^n := by
        apply sum_le_sum;intro n _
        exact (tail_bound a q _ (by omega) ht ht₁.le).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : n≤q+2+n)) (pow_nonneg ht.le _))
      _ ≤ _ := by rw [←Finset.mul_sum];exact mul_le_mul_of_nonneg_left (geometric N) (pow_nonneg ht.le _)
  rw [difference]
  exact (norm_add_le ..).trans ((add_le_add (absolute a (q+1) ht.le) rest).trans_eq (by ring))

end YM.Integration.WilsonOrdinaryPivotAsymptotic


end
