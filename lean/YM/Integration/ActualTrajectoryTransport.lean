import YM.Integration.ActualNormalizedPush
import YM.MergeProof.South.Window

/-! Repeated conditional transport on one fixed physical history. Intermediate
vacuum densities cancel exactly. This gives a tower law and a uniform value
bound, not the represented registration or differentiated comparison budgets
needed to reapply the local analytic construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson RG MeasureTheory MergeProof.Accent
open scoped BigOperators

variable {G : Gauge} (C : Family G) {N p j k m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Transport a complete observable from level `j` to `m` using exactly the
selected history's kernels and its full vacuum at both ends. -/
def actualTransport (I : Config G (C.side j p) → E) (hm : m ≤ j)
    (V : Config G (C.side m p)) : E :=
  ((C.path.rep N p m).eval V)⁻¹ •
    gust C.path N p j (fun U => (C.path.rep N p j).eval U • I U) m hm V

variable (hC : C.Makes)
include hC

/-- Any integrable unnormalized source gives a defined actual conditional
integral after dividing by the incoming physical vacuum. A global bound on
the inverse vacuum is not required. -/
theorem actualDensityRatio_integrable (hm : m < N)
    {F : Config G (C.side (m+1) p) → E} (hF : Integrable F (prior G _))
    (V : Config G (C.side m p)) :
    Integrable (fun U => actualConditionalDensity C N p m V U •
      (((C.path.rep N p (m+1)).eval U)⁻¹ • F U)) (prior G _) := by
  have heq : (fun U => actualConditionalDensity C N p m V U •
      (((C.path.rep N p (m+1)).eval U)⁻¹ • F U)) =
      (fun U => ((C.path.rep N p m).eval V)⁻¹ •
        ((C.path.levels.clock.op m p).density (C.path.β N p (m+1)) U V • F U)) := by
    funext U
    unfold actualConditionalDensity
    rw [smul_smul, smul_smul]
    congr 1
    have hfine := (Multi.AxisShift.chosen_positive hC.wilson hm U).ne'
    have hcoarse := (Multi.AxisShift.chosen_positive hC.wilson hm.le V).ne'
    field_simp
  rw [heq]
  exact (StepData.push_slice (C.path.levels.transition_mass ..) V F hF).smul _

/-- Undo normalization at the actual intermediate representation, not at an
arbitrary equal-density re-expression. -/
theorem actualTransport_unnormalize (hj : j ≤ N)
    (I : Config G (C.side j p) → E) (hm : m ≤ j)
    (V : Config G (C.side m p)) :
    (C.path.rep N p m).eval V • actualTransport C (N := N) I hm V =
      gust C.path N p j (fun U => (C.path.rep N p j).eval U • I U) m hm V := by
  unfold actualTransport
  rw [smul_smul, mul_inv_cancel₀
    (Multi.AxisShift.chosen_positive hC.wilson (hm.trans hj) V).ne', one_smul]

theorem actualTransport_base (hj : j ≤ N)
    (I : Config G (C.side j p) → E) :
    actualTransport C (N := N) I (le_refl j) = I := by
  funext V
  unfold actualTransport
  rw [gust_base, smul_smul, inv_mul_cancel₀
    (Multi.AxisShift.chosen_positive hC.wilson hj V).ne', one_smul]

/-- Every step uses the same actual numerator and vacuum; no `Checked` receipt
or separate lower bound on the partition function is needed. -/
theorem actualTransport_step (hj : j ≤ N)
    (I : Config G (C.side j p) → E) (hm : m < j) :
    actualTransport C (N := N) I hm.le =
      actualAverage C (N := N) (actualTransport C (N := N) I hm) := by
  funext V
  rw [actualAverage_push]
  simp_rw [actualTransport_unnormalize C hC hj]
  unfold actualTransport
  rw [gust_step C.path N p j _ hm]

/-- Arbitrarily many actual steps retain the original uniform value bound. -/
theorem actualTransport_norm_le (hj : j ≤ N)
    {I : Config G (C.side j p) → E} {B : ℝ}
    (hI : ∀ U, ‖I U‖ ≤ B) (hm : m ≤ j)
    (V : Config G (C.side m p)) :
    ‖actualTransport C (N := N) I hm V‖ ≤ B := by
  induction hm using Nat.decreasingInduction with
  | self => rw [actualTransport_base C hC hj]; exact hI V
  | of_succ l hl ih =>
    rw [actualTransport_step C hC hj I hl]
    exact actualAverage_norm_le C hC (hl.trans_le hj) ih V

/-- Conditioning through any intermediate level equals direct transport.
All three endpoints use the same fixed `C`, `N`, and period. -/
theorem actualTransport_tower (hj : j ≤ N)
    (I : Config G (C.side j p) → E) (hk : k ≤ j) (hm : m ≤ k) :
    actualTransport C (N := N) (actualTransport C (N := N) I hk) hm =
      actualTransport C (N := N) I (hm.trans hk) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [actualTransport_base C hC (hk.trans hj)]
  | of_succ l hl ih =>
    rw [actualTransport_step C hC (hk.trans hj) _ hl,
      actualTransport_step C hC hj _ (hl.trans_le hk), ih]

theorem actualTransport_const [CompleteSpace E] (hj : j ≤ N)
    (v : E) (hm : m ≤ j) (V : Config G (C.side m p)) :
    actualTransport C (N := N) (fun _ => v) hm V = v := by
  induction hm using Nat.decreasingInduction with
  | self => rw [actualTransport_base C hC hj]
  | of_succ l hl ih =>
    rw [actualTransport_step C hC hj _ hl]
    simp_rw [show actualTransport C (N := N) (fun _ : Config G (C.side j p) => v) hl =
      (fun _ => v) from funext ih]
    exact actualAverage_const C hC (hl.trans_le hj) v V

/-- Every transported coefficient is an actual integrable density when the
initial observable is measurable and bounded. -/
theorem actualTransport_weighted_integrable (hj : j ≤ N)
    {I : Config G (C.side j p) → E} {B : ℝ}
    (hI : AEStronglyMeasurable I (prior G _)) (hB : ∀ U, ‖I U‖ ≤ B)
    (hm : m ≤ j) :
    Integrable (fun U => (C.path.rep N p m).eval U •
      actualTransport C (N := N) I hm U) (prior G _) := by
  simp_rw [actualTransport_unnormalize C hC hj]
  apply gust_live C.path
  have hD := ((C.path.rep N p j).envelope
    (hC.wilson.represents N p j hj).good).integrable (prior G _)
  apply (hD.norm.mul_const B).mono' (hD.aestronglyMeasurable.smul hI)
  filter_upwards [] with U
  change ‖(C.path.rep N p j).eval U • I U‖ ≤ _
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hB U) (norm_nonneg _)

/-- Normalized transport remains measurable and integrable at every actual
level. Thus the tower and contraction are not relying on default zero values
for undefined Bochner integrals. -/
theorem actualTransport_integrable (hj : j ≤ N)
    {I : Config G (C.side j p) → E} {B : ℝ}
    (hI : AEStronglyMeasurable I (prior G _)) (hB : ∀ U, ‖I U‖ ≤ B)
    (hm : m ≤ j) :
    Integrable (actualTransport C (N := N) I hm) (prior G _) := by
  have hW := actualTransport_weighted_integrable C hC hj hI hB hm
  have hD : AEStronglyMeasurable (fun U => ((C.path.rep N p m).eval U)⁻¹)
      (prior G _) := ((C.path.rep N p m).envelope
    (hC.wilson.represents N p m (hm.trans hj)).good).meas.inv.aestronglyMeasurable
  have he : (fun U => ((C.path.rep N p m).eval U)⁻¹ •
      ((C.path.rep N p m).eval U • actualTransport C (N := N) I hm U)) =
      actualTransport C (N := N) I hm := by
    funext U
    rw [smul_smul, inv_mul_cancel₀
      (Multi.AxisShift.chosen_positive hC.wilson (hm.trans hj) U).ne', one_smul]
  refine Integrable.of_bound (he ▸ hD.smul hW.aestronglyMeasurable) B ?_
  exact ae_of_all _ (actualTransport_norm_le C hC hj hB hm)

/-- The full physical numerator is preserved after any number of steps. -/
theorem actualTransport_mass [CompleteSpace E] (hj : j ≤ N)
    {I : Config G (C.side j p) → E} {B : ℝ}
    (hI : AEStronglyMeasurable I (prior G _)) (hB : ∀ U, ‖I U‖ ≤ B)
    (hm : m ≤ j) :
    (∫ U, (C.path.rep N p m).eval U • actualTransport C (N := N) I hm U
      ∂prior G _) = ∫ U, (C.path.rep N p j).eval U • I U ∂prior G _ := by
  simp_rw [actualTransport_unnormalize C hC hj]
  apply gust_sum C.path
  have h := actualTransport_weighted_integrable C hC hj hI hB (le_refl j)
  rwa [actualTransport_base C hC hj] at h

open Marker Overlay Extra.Trajectories RG3.Law
variable {V : Type} [DecidableEq V]
    (q : Probes C V N p) (R : Census V)

/-- The literal existing physical insertion coefficients obey the same
normalized one-step law. No marked-deck `Checked`, `Active`, or budget
hypothesis is introduced to restate their already defined numerator. -/
theorem actualPhysicalRatio_step (hm : m < N)
    (s : R.Mode) (U : Config G (C.side m p)) :
    (coarseRatio q m R U).part s =
      Ride.bump ((C.S.block m).val : ℝ) s q.d *
        actualAverage C (N := N)
          (fun W => (coarseRatio q (m+1) R W).part s) U := by
  have he (W : Config G (C.side (m+1) p)) :
      (C.path.rep N p (m+1)).eval W • (coarseRatio q (m+1) R W).part s =
        (fineModel q (m+1) R W).part s := by
    rw [scaler_of, denom_eq hC hm, Complex.real_smul, Complex.ofReal_inv]
    have hn := Complex.ofReal_ne_zero.mpr
      (Multi.AxisShift.chosen_positive hC.wilson hm W).ne'
    field_simp
  rw [scaler_of, passing q hm, denom_eq hC hm.le, actualAverage_push]
  simp_rw [he]
  rw [Complex.real_smul, Complex.ofReal_inv]
  ring

omit hC in
theorem actualAverage_complex_mul
    (F : Config G (C.side (m+1) p) → ℂ) (c : ℂ)
    (U : Config G (C.side m p)) :
    actualAverage C (N := N) (fun W => c * F W) U =
      c * actualAverage C (N := N) F U := by
  unfold actualAverage
  simp_rw [Complex.real_smul, mul_left_comm _ c]
  rw [integral_const_mul]

omit hC in
private lemma actual_bump_step (s : R.Mode) :
    Ride.bump ((C.S.block m).val : ℝ) s q.d *
      Ride.bump (C.S.a (m+1)) s q.d = Ride.bump (C.S.a m) s q.d := by
  unfold Ride.bump
  rw [← Finset.prod_mul_distrib, C.S.a_step]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← mul_pow, Complex.ofReal_div]
  congr 1
  have hn : ((C.S.block m).val : ℂ) ≠ 0 := by
    exact_mod_cast (C.S.block m).property.ne'
  push_cast
  field_simp

/-- Complete physical insertion coefficients at every actual level are the
same normalized transport of the original literal product, with precisely the
original engineering factor at that level. -/
theorem actualPhysicalRatio_transport (hm : m ≤ N)
    (s : R.Mode) (U : Config G (C.side m p)) :
    (coarseRatio q m R U).part s = Ride.bump (C.S.a m) s q.d *
      actualTransport C (N := N) (fun W => ∏ i ∈ s.val, q.eval i W) hm U := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [actualTransport_base C hC (le_refl N), scaler_of, at_top,
      denom_eq hC (le_refl N), (hC.wilson.starts N p).2, Complex.ofReal_inv]
    have hn := Complex.ofReal_ne_zero.mpr (bare_pos (C.beta N p) U).ne'
    field_simp
  | of_succ l hl ih =>
    rw [actualPhysicalRatio_step C hC q R hl,
      actualTransport_step C hC (le_refl N) _ hl]
    simp_rw [ih]
    rw [actualAverage_complex_mul, ← mul_assoc, actual_bump_step C q R]

/-- Per-insertion bounds propagate through arbitrarily many actual levels
without an additional volume, depth, or normalization factor. The explicit
engineering factor is retained. -/
theorem actualPhysicalRatio_norm_le (hm : m ≤ N)
    (A : V → ℝ) (hA : ∀ i U, ‖q.eval i U‖ ≤ A i)
    (s : R.Mode) (U : Config G (C.side m p)) :
    ‖(coarseRatio q m R U).part s‖ ≤
      ‖Ride.bump (C.S.a m) s q.d‖ * ∏ i ∈ s.val, A i := by
  rw [actualPhysicalRatio_transport C hC q R hm, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply actualTransport_norm_le C hC (le_refl N) _ hm U
  intro W
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hA i W)

end YM.Integration
