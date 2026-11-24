import YM.Integration.WilsonLocalKernelConcentration

/-! A logarithmically shrinking neighborhood of the genuine multi-link Wilson
kernel costs less than every power, independently of the surrounding lattice. -/
noncomputable section
namespace YM.Integration.WilsonLocalKernelWindow
open YM RG RG02 Lattice Wilson MeasureTheory PowerSeries Filter
open WilsonKernelCoupling WilsonLocalKernelConcentration WilsonLocalKernelTemperature
open PertExtension.Series PertExtension.Series.Tested
open scoped Topology BigOperators
variable {c f : Side} (S : StepData c f) {G : Gauge}

def probability (A : Finset (Edge (Site c))) (b u : ℝ) (U : Config G f) : ℝ :=
  ∑ z, S.likelihood U z * ∫ V in {V | u ≤ score S A (S.prediction U z) V},
    S.noise b (S.prediction U z) V ∂prior G c

theorem uniform {G : Gauge} (D : Calendar G) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ (t : ℝ) in Tested.germ, ∀ m p : ℕ,
      (D.op m p).patch.Branches D.kernel G →
      ∀ (A : Finset (Edge (Site (D.schedule.side m p)))), A.card = k →
      ∀ (U : Config G (D.schedule.side (m+1) p)) (u : ℝ),
        probability (D.op m p) A (t^2)⁻¹ u U ≤ C * Real.exp (-(3/4:ℝ)*(t^2)⁻¹*u) := by
  let M := ‖coeff 0 (series (D.op 0 0) G 2)‖ + 1
  have hM : 0 < M := by dsimp only [M]; positivity
  have H := (all_orders (D.op 0 0) G (r:=2) (by norm_num)).tendsto_first.norm
  have H' : ∀ᶠ (t : ℝ) in Tested.germ, ‖ratio (D.op 0 0) G 2 t‖ < M :=
    H.eventually (eventually_lt_nhds (lt_add_one _))
  refine ⟨M^k, pow_pos hM _, ?_⟩
  filter_upwards [H',Tested.eventually_pos] with t ht hpos m p hB A hA U u
  have hg : (t^2)⁻¹ - ((2*t)^2)⁻¹ = (3/4:ℝ)*(t^2)⁻¹ := by
    field_simp [hpos.ne']
    ring
  have hnon : 0 ≤ (t^2)⁻¹ - ((2*t)^2)⁻¹ := by rw [hg]; positivity
  have hbound := physical (D.op m p) hB A (t^2)⁻¹ u hnon U
  rw [sub_sub_cancel, hg, neg_mul] at hbound
  have hR : (D.op m p).penaltyZ ((2*t)^2)⁻¹ G / (D.op m p).penaltyZ (t^2)⁻¹ G ≤ M := by
    have h := ht.le
    unfold ratio at h
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (div_pos ((D.op 0 0).penaltyZ_pos _) ((D.op 0 0).penaltyZ_pos _))] at h
    exact h
  refine hbound.trans ?_
  rw [hA, mul_comm (Real.exp _)]
  simpa only [neg_mul] using (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (div_pos ((D.op m p).penaltyZ_pos _) ((D.op m p).penaltyZ_pos _)).le hR k)
    (Real.exp_pos (-(3/4:ℝ)*(t^2)⁻¹*u)).le)

theorem logarithmic {G : Gauge} (D : Calendar G) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ᶠ (t : ℝ) in Tested.germ, ∀ m p : ℕ,
      (D.op m p).patch.Branches D.kernel G →
      ∀ (A : Finset (Edge (Site (D.schedule.side m p)))), A.card = k →
      ∀ (U : Config G (D.schedule.side (m+1) p)),
        probability (D.op m p) A (t^2)⁻¹ (t^2 * (Real.log t)^2) U ≤ C*t^n := by
  obtain ⟨C,hC,H⟩ := uniform D k
  refine ⟨C,hC,fun n => ?_⟩
  filter_upwards [H, Tested.eventually_pos, Tested.eventually_top (Real.exp_pos (-2*(n:ℝ)))] with t ht hp htop m p hB A hA U
  refine (ht m p hB A hA U _).trans (mul_le_mul_of_nonneg_left ?_ hC.le)
  have hl : Real.log t < -2*(n:ℝ) := (Real.log_lt_log hp htop).trans_eq (Real.log_exp _)
  have hl0 : Real.log t ≤ 0 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hg : (n:ℝ) ≤ -(3/4:ℝ)*Real.log t := by linarith
  calc
    _ = Real.exp (-(3/4:ℝ)*(Real.log t)^2) := by
      congr 1
      field_simp [hp.ne']
    _ ≤ Real.exp ((n:ℝ)*Real.log t) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonpos_right hg hl0]
    _ = t^n := by rw [Real.exp_nat_mul, Real.exp_log hp]

end YM.Integration.WilsonLocalKernelWindow
