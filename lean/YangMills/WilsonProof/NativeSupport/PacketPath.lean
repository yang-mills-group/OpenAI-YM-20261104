import YangMills.WilsonProof.NativeSupport.PacketMGF
import YangMills.WilsonProof.NativeSupport.TorusCopies

/-! Normalized physical word means on the original tagged trajectory, also
at a real, spatially homogeneous, off-calibration array. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Finset MeasureTheory Lattice RG Wilson RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance
open scoped Classical BigOperators
variable {G : Gauge} {n c : Side}

abbrev mean (d : Descent n c) (β : ℕ→ℝ) (f : Config G n→ℝ) (Z : Config G c) :=
  mass d β f Z / mass d β 1 Z

theorem mean_unit (d : Descent n c) (ok : d.OK G) (β : ℕ→ℝ) (Z : Config G c)
    {f : Config G n→ℝ} (h : Continuous f) (unit : ∀ U,|f U| ≤ 1) :
    |mean d β f Z| ≤ 1 := by
  rw [mean,abs_div,abs_of_pos (positive d ok β Z),div_le_one (positive d ok β Z)]
  refine (abs_sum_le_sum_abs ..).trans (sum_le_sum fun t _=>?_ )
  refine (norm_integral_le_integral_norm _).trans (integral_mono
    (d.path_integrable ok β t f h Z).norm (d.path_integrable ok β t 1 continuous_const Z) ?_)
  intro x
  simp only [Descent.integrand,Real.norm_eq_abs,abs_mul,Pi.one_apply,mul_one,
    abs_of_nonneg (d.probability_nonneg ..),abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_right (mul_nonneg (d.probability_nonneg ..) (Real.exp_pos _).le) (unit _)

theorem mean_sum {H : Type*} [Fintype H] (d : Descent n c) (ok : d.OK G) (β : ℕ→ℝ)
    (Z : Config G c) (F : H→ Config G n→ℝ) (h : ∀ j,Continuous (F j)) :
    mean d β (fun U=>∑ j,F j U) Z = ∑ j,mean d β (F j) Z := by
  unfold mean
  rw [←sum_div]
  congr 1
  unfold mass
  calc
    _ = ∑ t, ∑ j, ∫ x,d.integrand β t (F j) Z x ∂Descent.measure G d := by
      refine sum_congr rfl fun t _=>?_
      rw [←integral_finsetSum univ (fun j _=>d.path_integrable ok β t (F j) (h j) Z)]
      exact integral_congr_ae (.of_forall fun x=>by simp only [Descent.integrand,mul_sum])
    _ = _ := sum_comm

theorem translate_mean {A : Levels G} {per N k : ℕ} (T : Slices A per) (hk : k ≤ N)
    (b : Site (A.S.side k per)) (f : Config G (A.S.side N per)→ℝ) (h : Continuous f)
    (β : ℕ→ℝ) (sym : GaugeInvariant f) :
    let d := traversal T hk
    let F := fun U=>f (pull 1 (liftSite d b) U)
    GaugeInvariant F → mean d β F 1 = mean d β f 1 := by
  intro d F symF
  have cF : Continuous F := h.comp (continuous_pull ..)
  have both : GaugeInvariant (fun U=>F U-f U) := fun g U=>congrArg₂ (·-·) (symF g U) (sym g U)
  have changeMean := fraction d (traversal_ok T hk) β 1 (cF.sub h) both
  have equal := translated_read T hk b f h β
  change d.conditioned β (fun U=>F U-f U) 1=0 at equal
  have sub : mass d β (fun U=>F U-f U) 1 = mass d β F 1 - mass d β f 1 := by
    simp only [mass,←sum_sub_distrib]
    apply sum_congr rfl
    intro t _
    rw [←integral_sub (d.path_integrable (traversal_ok T hk) β t F cF 1)
      (d.path_integrable (traversal_ok T hk) β t f h 1)]
    exact integral_congr_ae (.of_forall fun x=> by simp only [Descent.integrand,mul_sub])
  unfold mean
  apply sub_eq_zero.mp
  rw [←sub_div,←sub]
  exact changeMean.symm.trans equal

end YM.Integration.InletSusceptibility.Packet
