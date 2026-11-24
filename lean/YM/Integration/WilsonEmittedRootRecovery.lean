import YM.Integration.WilsonEmittedWordJointFare
import YM.Comparison.RG02.Assembly.Clipper

/-! A paid root reports its radial angular coefficient with unit coupling
direction. Those reports determine the full joint derivatives, including
the direction with a held coupling. Their cancellation is applied before
the real Taylor remainder on a nonflat short chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedRootRecovery
open Set Function Comparison.RG02 Comparison.Density AnalyticBridge.SectorAffine.Offset
open scoped Classical ContDiff Topology
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem continuous_read (f : ℝ × E → F) (j : ℕ) (A : E) :
    Continuous (fun t : ℝ => Assembly.jet f j (t,A)) := by
  unfold Assembly.jet
  apply Continuous.const_smul
  apply (iteratedFDeriv ℝ j f 0).cont.comp
  exact continuous_pi fun _ => continuous_id.prodMk continuous_const

theorem joint (f h : ℝ × E → F) (j : ℕ) (hf : ContDiffAt ℝ ω f 0)
    (hh : ContDiffAt ℝ ω h 0)
    (read : ∀ A : E, Assembly.jet f j (1,A) = Assembly.jet h j (1,A)) :
    iteratedFDeriv ℝ j f 0 = iteratedFDeriv ℝ j h 0 := by
  apply Tensor.ext_diag _ _ hf.iteratedFDeriv_comp_perm hh.iteratedFDeriv_comp_perm
  funext z
  have line (A : E) {t : ℝ} (ht : t ≠ 0) :
      Assembly.jet f j (t,A) = Assembly.jet h j (t,A) := by
    have d : t • ((1:ℝ),t⁻¹ • A) = (t,A) := by
      ext <;> simp [smul_smul, ht]
    rw [←d, Assembly.Clipper.weight, Assembly.Clipper.weight, read]
  have across := Continuous.ext_on (dense_compl_singleton (0:ℝ))
    (continuous_read f j z.2) (continuous_read h j z.2)
    (fun t ht => line z.2 (by simpa using ht))
  exact (smul_right_injective F (inv_ne_zero (by exact_mod_cast j.factorial_ne_zero)))
    (congr_fun across z.1)

theorem tested (f h : ℝ × E → F) {j m : ℕ} {w D : ℝ}
    (hf : ContDiffAt ℝ ω f 0) (hh : ContDiffAt ℝ ω h 0)
    (read : ∀ i < j, ∀ A : E, Assembly.jet f i (1,A) = Assembly.jet h i (1,A))
    (hD : 0 ≤ D) (hw : 0 ≤ w) (hw' : w ≤ 1) (hm : j ≤ m)
    (funded : ∀ z : ℝ × E, ‖z‖ ≤ w → Through m (f-h) z D)
    (z : ℝ × E) (hz : ‖z‖ ≤ 1) :
    Through m ((f-h) ∘ Transport.dilation (ℝ × E) w) z (D*w^j) := by
  have old (i : ℕ) (hi : i < j) : ‖iteratedFDeriv ℝ i (f-h) 0‖ ≤ 0 := by
    rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hh.of_le le_top),
      joint f h i hf hh (read i hi), sub_self, norm_zero]
  simpa only [mul_zero,zero_add] using Transport.rescale j m w D 0 (f-h)
    hw hw' hD le_rfl hm funded old z hz

end YM.Integration.WilsonEmittedRootRecovery
