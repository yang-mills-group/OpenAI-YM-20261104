import YM.SectorNext.VACUUM_NORMALIZATION.Stripped
import YM.Source.Construction

/-!
# Some real normalization controls that survive reclosures

`IsKernel.total` is **not** a normalization asserted over the fine variable.
For real parameters we get instead an exact denominator, positive everywhere,
for the *actual interacting* conditional measure on that variable; record here
a couple bounds on it. Changing a set of output bonds uses only their costs,
not the volume or a product of clock prices for the finer scales. Use this sort
of estimate relatively -- no bill for dividing two independently estimated
exponentially big/small things. This doesn't yet pay iterated function-space
or complex marker estimates, nor make unrestricted coarse-field changes cheap.

We don't even need the kernel formula to hold *mask by mask* separately; these
identifications are invariant under re-expression preserving the full `eval`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.IterationFour.Denominator
open RG Wilson Lattice SectorNext.Vacuum Function MeasureTheory Filter
open scoped BigOperators Topology
variable {G : Gauge}

section Step
variable {c f : Side} (S : StepData c f) (β : ℝ)

def fee (u v : G.El) : ℝ := |β| * S.kernel.penalty * (2*G.chord (u*v⁻¹))
/-- The full expense; zero at every untouched link. -/
def expense (V W : Config G c) : ℝ := ∑ b, fee S β (V b) (W b)

lemma fee_symmetric (u v : G.El) : fee S β u v = fee S β v u := by
  unfold fee
  rw [← G.chord_inv (v*u⁻¹)]
  simp only [mul_inv_rev, inv_inv]

lemma expense_symmetric (V W : Config G c) : expense S β V W=expense S β W V := by
  unfold expense
  exact Finset.sum_congr rfl fun i _ => fee_symmetric ..

lemma bond_change (u v w : G.El) : S.penaltyWeight β (u*w⁻¹) ≤
    Real.exp (fee S β u v) * S.penaltyWeight β (v*w⁻¹) := by
  have h := price_compare (u*w⁻¹) (v*w⁻¹)
  rw [show u*w⁻¹ * (v*w⁻¹)⁻¹=u*v⁻¹ by group] at h
  unfold StepData.penaltyWeight
  rw [← Real.exp_add, Real.exp_le_exp]
  let k := -β * S.kernel.penalty
  have hk : |k|=|β| *S.kernel.penalty := by
    rw [abs_mul, abs_neg, abs_of_pos S.kernel.penalty_pos]
  have hx : k * (G.price (u*w⁻¹)-G.price (v*w⁻¹)) ≤ fee S β u v := by
    apply le_trans (le_abs_self _)
    rw [abs_mul, hk]
    exact mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg _) S.kernel.penalty_pos.le)
  change k * _ ≤ _ + k * _
  linarith only [hx]

lemma noise_change (Q V W : Config G c) : S.noise β Q V ≤ Real.exp (expense S β V W) * S.noise β Q W := by
  unfold StepData.noise expense
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  have hz := inv_pos.mpr (S.penaltyZ_pos β (G:=G))
  refine Finset.prod_le_prod (fun i _ => mul_nonneg hz.le (Real.exp_pos _).le) (fun i _ => ?_)
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (bond_change S β _ _ _) hz.le

lemma kernel_change (U : Config G f) (V W : Config G c) :
    S.density β U V ≤ Real.exp (expense S β V W) * S.density β U W := by
  unfold StepData.density; rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (noise_change ..) (S.likelihood_pos ..)

lemma relative_core (h : S.IsKernel β G) (F : Config G f → ℝ) (hp : Integrable F (prior G f))
    (hf : ∀ U, 0 ≤ F U) (V W : Config G c) :
    S.push β F V ≤ Real.exp (expense S β V W) * S.push β F W := by
  unfold StepData.push; rw [← integral_const_mul]
  refine integral_mono (StepData.push_slice h V _ hp)
    ((StepData.push_slice h W _ hp).const_mul _) ?_
  intro U
  dsimp only
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (kernel_change ..) (hf U)
lemma sparse (V W : Config G c) (T : Finset (Edge (Site c))) (h : ∀ i, i∉T → V i=W i) (t : ℝ)
    (ht : ∀ i∈T, G.chord (V i*(W i)⁻¹) ≤ t) :
    expense S β V W ≤ T.card*(|β| * S.kernel.penalty * (2*t)) := calc
  _ = ∑ i ∈ T, fee S β (V i) (W i) := by
    apply Eq.symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi; simp [h i hi, fee]
  _ ≤ ∑ _i ∈ T, (|β| *S.kernel.penalty*(2*t)) := Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ht _ hi) zero_le_two)
      (mul_nonneg (abs_nonneg _) S.kernel.penalty_pos.le)
  _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- Domination relative to the *same* unnormalized weight pays no denominator-in-volume costs.
    NOT an assertion that our source entries satisfy such a domination with small `a`! -/
lemma normalize_held {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h : S.IsKernel β G) {F : Config G f → ℝ} (hf : Integrable F (prior G f))
    (L : Config G f → X) (hl : Integrable L (prior G f))
    {a : ℝ} (hp : ∀ U, ‖L U‖ ≤ a*F U) (V : Config G c) (he : 0 < S.push β F V) :
    ‖S.push β L V‖ / S.push β F V ≤ a := by
  rw [div_le_iff₀ he]
  unfold StepData.push
  rw [← integral_const_mul]
  apply le_trans (norm_integral_le_integral_norm _)
  refine integral_mono ((StepData.push_slice h V _ hl).norm)
    ((StepData.push_slice h V _ hf).const_mul _) ?_
  intro U
  dsimp only
  rw [norm_smul, Real.norm_of_nonneg (h.positive U V), smul_eq_mul, mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hp U) (h.positive U V)
end Step
variable (C : Family G)
abbrev operator (q i : ℕ) := C.path.levels.clock.op i q

/-- Hold the indicated coarse configuration. Use actual H.beta ALWAYS, even when using a
    re-expression R that stores some b' different from R_old.beta. -/
def denominator (N q i : ℕ) (R : Rep G (C.side (i+1) q)) :=
    (operator C q i).push (C.path.β N q (i+1)) R.eval

def held (N q i : ℕ) (R : Rep G (C.side (i+1) q)) (V : Config G (C.side i q))
    (U : Config G (C.side (i+1) q)) :=
    (operator C q i).density (C.path.β N q (i+1)) U V * R.eval U /
      denominator C N q i R V

variable (hC : C.Makes) {N q i : ℕ} (h : i<N) (R : Rep G (C.side (i+1) q))
    (hR : R.eval=(C.path.rep N q (i+1)).eval)
include hC h hR

lemma denominator_real : denominator C N q i R=(C.path.rep N q i).eval := by
  rw [denominator,hR]
  exact (hC.wilson.steps _ _ _ h).1.symm

lemma denominator_pos (V) : 0 < denominator C N q i R V := by
  rw [denominator_real C hC h R hR]
  exact strictly C.path hC.wilson N q i h.le V

lemma denominator_paid (V W) :
    |Real.log (denominator C N q i R V)-Real.log (denominator C N q i R W)| ≤
      expense (operator C q i) (C.path.β N q (i+1)) V W := by
  have hz : ∀ V, 0 < denominator C N q i R V := denominator_pos C hC h R hR
  have hi : Integrable R.eval (prior G (C.side (i+1) q)) := by
    rw [hR]
    exact ((C.path.rep N q _).envelope
      (hC.wilson.represents N q _ h).good).integrable (prior G (C.side (i+1) q))
  have ht V W : Real.log (denominator C N q i R V) - Real.log (denominator C N q i R W) ≤
      expense (operator C q i) (C.path.β N q (i+1)) V W := by
    apply sub_le_iff_le_add.mpr
    rw [← Real.exp_le_exp, Real.exp_log (hz V), Real.exp_add, Real.exp_log (hz W)]
    exact relative_core _ _ (C.path.levels.transition_mass ..) R.eval hi
      (fun U => hR.symm ▸ (strictly _ hC.wilson _ _ _ h U).le) V W
  exact abs_le.mpr ⟨by rw [expense_symmetric _ _ V W]; linarith only [ht W V], ht V W⟩

lemma held_pos (V U) : 0 ≤ held C N q i R V U := by
  refine div_nonneg (mul_nonneg (StepData.density_positive ..) ?_) ((denominator_pos C hC h R hR V).le)
  rw [hR]
  exact (strictly _ hC.wilson _ _ _ h _).le
lemma held_norm (V) :
    Integrable (held C N q i R V) (prior G _) ∧
      (∫ U, held C N q i R V U ∂prior G _) = 1 := by
  constructor
  · apply (StepData.push_slice (C.path.levels.transition_mass i q (C.path.β N q (i+1))) V R.eval
      ?_).div_const _
    rw [hR]; exact ((C.path.rep N q _).envelope
      (hC.wilson.represents N q _ h).good).integrable _
  unfold held
  rw [integral_div]
  exact div_self (denominator_pos C hC h R hR V).ne'
end YM.IterationFour.Denominator
