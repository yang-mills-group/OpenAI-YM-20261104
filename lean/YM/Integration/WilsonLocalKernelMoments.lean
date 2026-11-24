import YM.Integration.WilsonLocalKernelWindow

/-! Physical moments of the total observed energy, at the scale of one Wilson step. -/
noncomputable section
namespace YM.Integration.WilsonLocalKernelMoments
open YM RG Lattice Wilson MeasureTheory Set Filter PowerSeries
open WilsonLocalKernelConcentration WilsonLocalKernelTemperature
open PertExtension.Series PertExtension.Series.Tested
open scoped BigOperators Topology
variable {c f : Side} {G : Gauge} (S : StepData c f)

theorem nonneg (A : Finset (Edge (Site c))) (Q V : Config G c) :
    0 ≤ score S A Q V := Finset.sum_nonneg fun _ _ =>
  mul_nonneg S.kernel.penalty_pos.le (G.price_range _).1

theorem power {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h) (n : ℕ) :
    x^n ≤ ((n.factorial:ℝ)/h^n) * Real.exp (h*x) := by
  have hf : 0 < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have ht := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (h*x) (mul_nonneg hh.le hx) n)
  calc
    _ ≤ Real.exp (h*x)*(n.factorial:ℝ)/h^n := (le_div_iff₀ (pow_pos hh n)).mpr (by
      simpa only [mul_pow, mul_comm (x^n)] using ht)
    _ = _ := by ring

theorem bounded (A : Finset (Edge (Site c))) (Q : Config G c) (b : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (∫ V, S.noise b Q V * (score S A Q V)^n ∂prior G c) ≤
      ((n.factorial:ℝ)/h^n) * (S.penaltyZ (b-h) G / S.penaltyZ b G)^A.card := by
  letI : IsFiniteMeasureOnCompacts (prior G c) :=
    inferInstanceAs (IsFiniteMeasureOnCompacts (Measure.pi fun _ : Edge (Site c) => G.probHaar))
  have hc : Continuous (fun V => S.noise b Q V * Real.exp (h*score S A Q V)) :=
    ((S.noise_cont b).comp (continuous_const.prodMk continuous_id)).mul
      (Real.continuous_exp.comp (continuous_const.mul (score_continuous S A Q)))
  have hi := hc.integrable_of_hasCompactSupport (μ:=prior G c) (HasCompactSupport.of_compactSpace _)
  have hn (V : Config G c) : 0 ≤ S.noise b Q V :=
    Finset.prod_nonneg fun i _ => mul_nonneg (inv_pos.mpr (S.penaltyZ_pos b)).le (Real.exp_pos _).le
  rw [← moment S A b h Q, ← integral_const_mul]
  apply integral_mono_of_nonneg (ae_of_all _ fun V => mul_nonneg (hn V) (pow_nonneg (nonneg S A Q V) n))
    (hi.const_mul _) (ae_of_all _ fun V => ?_)
  exact (mul_le_mul_of_nonneg_left (power (nonneg S A Q V) hh n) (hn V)).trans_eq (by ring)

def joint (A : Finset (Edge (Site c))) (b : ℝ) (n : ℕ) (U : Config G f) : ℝ :=
  ∑ z, S.likelihood U z * ∫ V, S.noise b (S.prediction U z) V *
    (score S A (S.prediction U z) V)^n ∂prior G c

theorem tilted (hB : S.patch.Branches S.kernel G) (A : Finset (Edge (Site c)))
    (b : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) (U : Config G f) :
    joint S A b n U ≤ ((n.factorial:ℝ)/h^n) * (S.penaltyZ (b-h) G / S.penaltyZ b G)^A.card := by
  calc
    _ ≤ ∑ z, S.likelihood U z * (((n.factorial:ℝ)/h^n) * (S.penaltyZ (b-h) G / S.penaltyZ b G)^A.card) :=
      Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (bounded S A _ b hh n) (S.likelihood_pos U z)
    _ = _ := by rw [← Finset.sum_mul,S.chosen hB,one_mul]

theorem calendar {G : Gauge} (D : Calendar G) (k : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ (t : ℝ) in Tested.germ, ∀ (n m p : ℕ),
      (D.op m p).patch.Branches D.kernel G →
      ∀ (A : Finset (Edge (Site (D.schedule.side m p)))), A.card = k →
      ∀ U : Config G (D.schedule.side (m+1) p),
        joint (D.op m p) A (t^2)⁻¹ n U ≤ ((n.factorial:ℝ)*((4/3:ℝ)*t^2)^n)*M := by
  let B := ‖coeff 0 (series (D.op 0 0) G 2)‖+1
  have hB : 0 < B := by dsimp only [B]; positivity
  have H := (all_orders (D.op 0 0) G (r:=2) (by norm_num)).tendsto_first.norm
  have H' : ∀ᶠ (t : ℝ) in Tested.germ, ‖ratio (D.op 0 0) G 2 t‖ < B :=
    H.eventually (eventually_lt_nhds (lt_add_one _))
  refine ⟨B^k,pow_pos hB _,?_⟩
  filter_upwards [H',Tested.eventually_pos] with t ht hpos n m p hBR A hA U
  have hg : (t^2)⁻¹ - ((2*t)^2)⁻¹ = (3/4:ℝ)*(t^2)⁻¹ := by
    field_simp [hpos.ne']
    ring
  have hposh : 0 < (t^2)⁻¹ - ((2*t)^2)⁻¹ := by rw [hg]; positivity
  have he : ((t^2)⁻¹ - ((2*t)^2)⁻¹)⁻¹ = (4/3:ℝ)*t^2 := by rw [hg]; field_simp
  have hin := tilted (D.op m p) hBR A (t^2)⁻¹ hposh n U
  rw [sub_sub_cancel,hA,div_eq_mul_inv (n.factorial:ℝ),←inv_pow ((t^2)⁻¹ - ((2*t)^2)⁻¹) n,he] at hin
  have hr : (D.op m p).penaltyZ ((2*t)^2)⁻¹ G / (D.op m p).penaltyZ (t^2)⁻¹ G ≤ B := by
    have h := ht.le
    unfold ratio at h
    rw [← Complex.ofReal_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
      (div_pos ((D.op 0 0).penaltyZ_pos _) ((D.op 0 0).penaltyZ_pos _))] at h
    exact h
  exact hin.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (div_pos ((D.op m p).penaltyZ_pos _) ((D.op m p).penaltyZ_pos _)).le hr k) (by positivity))

end YM.Integration.WilsonLocalKernelMoments
