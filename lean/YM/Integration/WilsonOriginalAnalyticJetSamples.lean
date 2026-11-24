import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Coefficient recovery at the actual sampled heaters of the analytic point
upgrade. Only convergence of the rescaled heaters is used. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAnalyticJetSamples
open Function Filter Finset Matrix
open scoped BigOperators Topology
variable {X : Type*} {l : Filter X} {n : ℕ}

private def mass (A : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ j, ∑ i, ‖A j i‖

private lemma entry (A : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) :
    ‖A j i‖ ≤ mass A := by
  exact (Finset.single_le_sum (fun k _ => norm_nonneg (A j k)) (Finset.mem_univ i)).trans
    (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun t _ => norm_nonneg (A k t)))
      (Finset.mem_univ j))

private theorem enrolled (node : X → Fin n → ℂ) (c : Fin n → ℂ) (hc : Injective c)
    (h : ∀ i, Tendsto (fun x => node x i) l (𝓝 (c i))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x in l, IsUnit (vandermonde (node x)).det ∧
      ∀ j i, ‖(vandermonde (node x))⁻¹ j i‖ ≤ B := by
  let A := vandermonde c
  have detpos : A.det ≠ 0 := det_vandermonde_ne_zero_iff.mpr hc
  have tv : Tendsto (fun x => vandermonde (node x)) l (𝓝 A) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => (h i).pow j.val
  have td : Tendsto (fun x => (vandermonde (node x)).det) l (𝓝 A.det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp tv
  have idet : ContinuousAt Ring.inverse A.det := by
    rw [show (Ring.inverse : ℂ → ℂ) = Inv.inv from funext fun x => Ring.inverse_eq_inv x]
    exact continuousAt_inv₀ detpos
  have ti := (continuousAt_matrix_inv A idet).tendsto.comp tv
  have cm : Continuous (mass (n:=n)) := by unfold mass; fun_prop
  have upper := ((cm.tendsto _).comp ti).eventually_lt_const (lt_add_one (mass A⁻¹))
  refine ⟨mass A⁻¹ + 1,add_nonneg (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun i _ => norm_nonneg (A⁻¹ j i)) zero_le_one,?_⟩
  filter_upwards [td.eventually_ne detpos,upper] with x hx ux
  exact ⟨isUnit_iff_ne_zero.mpr hx,fun j i => (entry _ j i).trans ux.le⟩

/-- The coefficient of order j costs the j-th power of the scale on the
actual sampling dates, uniformly in the Fourier mode and its sampled data. -/
theorem original (warm : ℝ → ℝ) (date : X → Fin n → ℝ) (scale : X → ℂ)
    (hs : ∀ᶠ x in l, scale x ≠ 0) (c : Fin n → ℂ) (hc : Injective c)
    (sample : ∀ i, Tendsto (fun x => scale x * (warm (date x i) : ℂ)) l (𝓝 (c i))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ x in l, ∀ (f a : Fin n → ℂ) (j : Fin n),
      ‖f j‖ ≤ ‖scale x‖ ^ j.val * B *
        ∑ i, (‖a i‖ + ‖a i - ∑ k : Fin n, (warm (date x i) : ℂ)^k.val * f k‖) := by
  let node x i := scale x * (warm (date x i) : ℂ)
  obtain ⟨B,hB,bought⟩ := enrolled node c hc sample
  refine ⟨B,hB,?_⟩
  filter_upwards [bought,hs] with x hx hscale f a j
  let A := vandermonde (node x)
  let u (k : Fin n) := f k / (scale x)^k.val
  let y (i : Fin n) := ∑ k : Fin n, (warm (date x i) : ℂ)^k.val * f k
  have appears : A *ᵥ u = y := by
    funext i
    change (∑ k : Fin n, (scale x * (warm (date x i) : ℂ))^k.val * (f k / (scale x)^k.val)) = _
    unfold y
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow]
    field_simp [hscale]
  have readback : A⁻¹ *ᵥ y = u := by
    rw [←appears,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hx.1,Matrix.one_mulVec]
  have report : ‖u j‖ ≤ B * ∑ i, (‖a i‖ + ‖a i-y i‖) := by
    rw [←readback,Matrix.mulVec, dotProduct,Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hx.2 j i) (by simpa only [sub_sub_cancel] using norm_sub_le (a i) (a i-y i))
      (norm_nonneg _) hB
  have pay : f j = (scale x)^j.val * u j := by dsimp [u]; field_simp [hscale]
  calc
    ‖f j‖ = ‖scale x‖ ^ j.val * ‖u j‖ := by conv_lhs => rw [pay,norm_mul,norm_pow]
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left report (pow_nonneg (norm_nonneg _) _)

end YM.Integration.WilsonOriginalAnalyticJetSamples
end
