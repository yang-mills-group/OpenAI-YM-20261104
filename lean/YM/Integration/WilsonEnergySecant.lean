import Mathlib.Analysis.Calculus.LocalExtr.Basic
import YM.Integration.WilsonLinkEnergy

/-! The measured Wilson energy and the temperature derivative of its Gaussian normalization. -/
noncomputable section
namespace YM.Integration.WilsonEnergySecant
open YM RG RG02 RG02.Asym Lattice Wilson MeasureTheory Filter
open PertExtension.Series PertExtension.Series.Tested WilsonKernelCoupling WilsonLinkEnergy
open WilsonLocalKernelTemperature
open scoped Topology
variable {c f : Side} (S : StepData c f) (G : Gauge)

theorem affine (b h : ℝ) :
    1+(h*S.kernel.penalty)*energy S G b ≤ S.penaltyZ (b-h) G / S.penaltyZ b G := by
  let ρ := link S b (1:G.El)
  let x (g : G.El) := (h*S.kernel.penalty)*G.price g
  have hρ : Continuous ρ := by unfold ρ link StepData.penaltyWeight; fun_prop
  have hx : Continuous x := continuous_const.mul G.continuous_price
  have hI (F : G.El → ℝ) (hF : Continuous F) : Integrable F G.probHaar :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : (∫ g, ρ g ∂G.probHaar) = 1 := link_mass S b 1
  have he : (∫ g, ρ g * x g ∂G.probHaar) = (h*S.kernel.penalty)*energy S G b := by
    rw [WilsonLinkEnergy.energy,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with g
    unfold ρ x
    ring
  have hi : Integrable (fun g => ρ g*x g) G.probHaar := hI _ (hρ.mul hx)
  calc
    _ = ∫ g, ρ g + ρ g*x g ∂G.probHaar := by
      rw [integral_add (hI _ hρ) hi,hm,he]
    _ ≤ ∫ g, ρ g*Real.exp (x g) ∂G.probHaar := by
      apply integral_mono (hI _ (hρ.add (hρ.mul hx))) (hI _ (hρ.mul (Real.continuous_exp.comp hx)))
      intro g
      change ρ g + ρ g*x g ≤ ρ g*Real.exp (x g)
      have hstep : 1+x g ≤ Real.exp (x g) := by linarith only [Real.add_one_le_exp (x g)]
      simpa only [mul_add,mul_one] using mul_le_mul_of_nonneg_left hstep (link_pos S b 1 g).le
    _ = _ := tilt S G b h

def normalized (t : ℝ) := (t^2)⁻¹*S.kernel.penalty*energy S G (t^2)⁻¹

theorem slope (r t : ℝ) :
    (1-(r^2)⁻¹)*normalized S G t ≤
      S.penaltyZ ((r*t)^2)⁻¹ G / S.penaltyZ (t^2)⁻¹ G - 1 := by
  have hr : (t^2)⁻¹-((r*t)^2)⁻¹ = (1-(r^2)⁻¹)*(t^2)⁻¹ := by
    rw [mul_pow,mul_inv_rev]
    ring
  have H := affine S G (t^2)⁻¹ ((t^2)⁻¹-((r*t)^2)⁻¹)
  rw [sub_sub_cancel,hr] at H
  unfold normalized
  linarith only [H]

theorem real_ratio {r : ℝ} (hr : 0 < r) :
    Tendsto (fun t : ℝ => S.penaltyZ ((r*t)^2)⁻¹ G / S.penaltyZ (t^2)⁻¹ G)
      Tested.germ (𝓝 (r^Friction.cardinal G)) := by
  have h := (all_orders S G hr).tendsto_first.norm
  rw [leading] at h
  have ht (t : ℝ) : ‖ratio S G r t‖ =
      S.penaltyZ ((r*t)^2)⁻¹ G / S.penaltyZ (t^2)⁻¹ G := by
    rw [ratio,← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (div_pos (S.penaltyZ_pos _) (S.penaltyZ_pos _))]
  simpa only [ht,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using h

/-- Every limiting normalized energy has the Gaussian value in the original Lie dimension. -/
theorem eq_of_limit {e : ℝ} {α : Type*} {l : Filter α} [NeBot l] {t : α → ℝ}
    (ht : Tendsto t l Tested.germ) (he : Tendsto (fun a => normalized S G (t a)) l (𝓝 e)) :
    e = (Friction.cardinal G : ℝ)/2 := by
  let d := Friction.cardinal G
  have H (r : ℝ) (hr : 0 < r) : (1-(r^2)⁻¹)*e ≤ r^d-1 :=
    le_of_tendsto_of_tendsto' (tendsto_const_nhds.mul he)
      (((real_ratio S G hr).comp ht).sub_const 1) (fun a => slope S G r (t a))
  let F (r : ℝ) := r^d-1-(1-(r^2)⁻¹)*e
  have hmin : IsLocalMin F 1 := by
    filter_upwards [eventually_gt_nhds (zero_lt_one : (0:ℝ)<1)] with r hr
    have h1 : F 1 = 0 := by simp [F]
    show F 1 ≤ F r
    rw [h1]
    exact sub_nonneg.mpr (H r hr)
  have hd : HasDerivAt F ((d:ℝ)-2*e) 1 := by
    have h₁ := (hasDerivAt_pow d (1:ℝ)).sub_const 1
    have h₂ := (hasDerivAt_pow 2 (1:ℝ)).inv (by norm_num)
    have h₃ := h₁.sub (((hasDerivAt_const (1:ℝ) (1:ℝ)).sub h₂).mul_const e)
    change HasDerivAt F _ (1:ℝ) at h₃
    simpa using! h₃
  have hz := hmin.hasDerivAt_eq_zero hd
  change e = (d:ℝ)/2
  linarith only [hz]

/-- The measured energy per link converges at the native positive temperature. -/
theorem equipartition :
    Tendsto (normalized S G) Tested.germ (𝓝 ((Friction.cardinal G : ℝ)/2)) := by
  let d := Friction.cardinal G
  have hn (t : ℝ) : 0 ≤ normalized S G t := by
    apply mul_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) S.kernel.penalty_pos.le)
    apply integral_nonneg
    intro g
    apply mul_nonneg (link_pos S _ 1 g).le
    exact (G.price_range g).1
  have hr := (real_ratio S G (r:=2) (by norm_num)).eventually
    (eventually_lt_nhds (lt_add_one ((2:ℝ)^d)))
  have hm : ∀ᶠ t in Tested.germ, normalized S G t ∈ Set.Icc 0 (2*(2:ℝ)^d) := by
    filter_upwards [hr] with t ht
    have H := slope S G 2 t
    have h₂ : 1-((2:ℝ)^2)⁻¹=3/4 := by norm_num
    rw [h₂] at H
    refine ⟨hn t,?_⟩
    have hp : 0 < (2:ℝ)^d := by positivity
    change S.penaltyZ ((2*t)^2)⁻¹ G / S.penaltyZ (t^2)⁻¹ G < (2:ℝ)^d+1 at ht
    linarith only [ht,H,hp]
  apply isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt hm
  intro e _ he
  obtain ⟨ψ,hψ,hg⟩ := he.exists_seq_tendsto
  exact eq_of_limit S G hg hψ

/-- One temperature window works for every calendar level and every period. -/
theorem calendar {G : Gauge} (D : Calendar G) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in Tested.germ, ∀ m p : ℕ,
      |normalized (D.op m p) G t-(Friction.cardinal G:ℝ)/2| < ε := by
  have h := (equipartition (D.op 0 0) G).eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [h] with t ht m p
  change |normalized (D.op 0 0) G t-(Friction.cardinal G:ℝ)/2| < ε
  simpa only [Metric.mem_ball,Real.dist_eq] using ht

end YM.Integration.WilsonEnergySecant
