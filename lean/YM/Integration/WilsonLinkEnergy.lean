import YM.Integration.WilsonLocalKernelMoments
import YM.Integration.WilsonLocalKernelLaplace

/-! The native one-link Wilson energy has a quadratic bound on the whole regulator calendar. -/
noncomputable section
namespace YM.Integration.WilsonLinkEnergy
open YM RG Lattice Wilson MeasureTheory Filter PowerSeries
open PertExtension.Series PertExtension.Series.Tested WilsonKernelCoupling WilsonLocalKernelTemperature
open scoped Topology
variable {c f : Side} (S : StepData c f) (G : Gauge)

def energy (b : ℝ) : ℝ := ∫ g, link S b 1 g * G.price g ∂G.probHaar

theorem tilt (b h : ℝ) :
    (∫ g, link S b 1 g * Real.exp ((h*S.kernel.penalty)*G.price g) ∂G.probHaar) =
      S.penaltyZ (b-h) G / S.penaltyZ b G := by
  have hw (g : G.El) : S.penaltyWeight ((b-h)-b) (g*1⁻¹) =
      Real.exp ((h*S.kernel.penalty)*G.price g) := by
    simp only [StepData.penaltyWeight,inv_one,mul_one]
    congr 1
    ring
  have hp (g : G.El) : link S b 1 g * Real.exp ((h*S.kernel.penalty)*G.price g) =
      (S.penaltyZ (b-h) G / S.penaltyZ b G) * link S (b-h) 1 g := by
    rw [← hw]
    exact WilsonLocalKernelLaplace.shifted S b (b-h) 1 g
  simp_rw [hp]
  rw [integral_const_mul,link_mass,mul_one]

theorem bound (b h : ℝ) :
    (h*S.kernel.penalty)*energy S G b ≤ S.penaltyZ (b-h) G / S.penaltyZ b G := by
  have hl : Continuous (link S b (1:G.El)) := by unfold link StepData.penaltyWeight; fun_prop
  have hx : Continuous (fun g : G.El => (h*S.kernel.penalty)*G.price g) :=
    continuous_const.mul G.continuous_price
  have hI (F : G.El → ℝ) (hc : Continuous F) : Integrable F G.probHaar :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ g, link S b 1 g * ((h*S.kernel.penalty)*G.price g) ∂G.probHaar := by
      rw [energy,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with g
      ring
    _ ≤ ∫ g, link S b 1 g * Real.exp ((h*S.kernel.penalty)*G.price g) ∂G.probHaar := by
      apply integral_mono (hI _ (hl.mul hx)) (hI _ (hl.mul (Real.continuous_exp.comp hx)))
      intro g
      apply mul_le_mul_of_nonneg_left _ (link_pos S b 1 g).le
      change (h*S.kernel.penalty)*G.price g ≤ Real.exp ((h*S.kernel.penalty)*G.price g)
      linarith only [Real.add_one_le_exp ((h*S.kernel.penalty)*G.price g)]
    _ = _ := tilt S G b h

theorem calendar {G : Gauge} (D : Calendar G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t in Tested.germ, ∀ m p : ℕ,
      energy (D.op m p) G (t^2)⁻¹ ≤ C*t^2 := by
  let B := ‖coeff 0 (series (D.op 0 0) G 2)‖+1
  have hB : 0 < B := by dsimp only [B]; positivity
  have H := (all_orders (D.op 0 0) G (r:=2) (by norm_num)).tendsto_first.norm
  have HR : ∀ᶠ t in Tested.germ, ‖ratio (D.op 0 0) G 2 t‖ < B :=
    H.eventually (eventually_lt_nhds (lt_add_one _))
  have hD := D.kernel.penalty_pos
  refine ⟨((4/3:ℝ)*B) / D.kernel.penalty,by positivity,?_⟩
  filter_upwards [HR,Tested.eventually_pos] with t ht hpos m p
  have hg : (t^2)⁻¹ - ((2*t)^2)⁻¹ = (3/4:ℝ)*(t^2)⁻¹ := by field_simp [hpos.ne']; ring
  have hr := ht.le
  unfold ratio at hr
  rw [← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos
    (div_pos ((D.op 0 0).penaltyZ_pos _) ((D.op 0 0).penaltyZ_pos _))] at hr
  have hb := bound (D.op m p) G (t^2)⁻¹ ((t^2)⁻¹-((2*t)^2)⁻¹)
  rw [sub_sub_cancel,hg] at hb
  have hw : 0 < (3/4:ℝ)*(t^2)⁻¹*D.kernel.penalty := by positivity
  have hx : energy (D.op m p) G (t^2)⁻¹ ≤ B / ((3/4:ℝ)*(t^2)⁻¹*D.kernel.penalty) := by
    apply (le_div_iff₀ hw).2
    rw [mul_comm]
    exact hb.trans hr
  apply hx.trans_eq
  field_simp [hpos.ne',hD.ne']

end YM.Integration.WilsonLinkEnergy
