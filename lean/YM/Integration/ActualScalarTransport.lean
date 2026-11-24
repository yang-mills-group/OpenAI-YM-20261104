import YM.Integration.ActualTrajectoryTransport
import YM.OPE.Therm.Law

/-! Scalar readout on the literal actual history. Weighted integrability is
enough to preserve means; a pointwise bound on a normalized forced remainder
is not required. Local scalar-error prices remain explicit inputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration
open Lattice Wilson RG MeasureTheory MergeProof.Accent OPE.Therm
open scoped BigOperators

variable {G : Gauge} (C : Family G) (hC : C.Makes) {N p j m : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
include hC

/-- The native unnormalized integrability receipt suffices at every actual
level, even when the normalized observable has no uniform pointwise bound. -/
theorem actualTransport_weighted_integrable_of_integrable (hj : j ≤ N)
    {F : Config G (C.side j p) → E}
    (hF : Integrable (fun U => (C.path.rep N p j).eval U • F U) (prior G _))
    (hm : m ≤ j) :
    Integrable (fun U => (C.path.rep N p m).eval U •
      actualTransport C (N := N) F hm U) (prior G _) := by
  simp_rw [actualTransport_unnormalize C hC hj]
  exact gust_live C.path N p j _ hF hm

/-- The same receipt gives an actual integrable observable for the native
selected-history probability measure. -/
theorem actualScene_integrable_of_weighted (hj : j ≤ N)
    {F : Config G (C.side j p) → E}
    (hF : Integrable (fun U => (C.path.rep N p j).eval U • F U) (prior G _)) :
    Integrable F (scene C.path N p j) := by
  unfold scene
  rw [integrable_withDensity_iff_integrable_smul'
    (dose_env hC.wilson hj).meas.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (dose_positive hC.wilson hj _).le,
    dose, div_eq_inv_mul, mul_smul]
  exact hF.smul ((partition G (C.side N p) (C.path.β N p N))⁻¹)

/-- The scalar normalization is the original Wilson partition at the fixed
cutoff, independent of the intermediate readout level. -/
theorem actualScene_formula (hj : j ≤ N) (F : Config G (C.side j p) → E) :
    (∫ U, F U ∂scene C.path N p j) =
      (partition G (C.side N p) (C.path.β N p N))⁻¹ •
        ∫ U, (C.path.rep N p j).eval U • F U ∂prior G _ := by
  rw [account hC.wilson hj]
  simp_rw [dose, div_eq_inv_mul, mul_smul]
  rw [integral_smul]

variable [CompleteSpace E]

/-- Full numerator preservation with precisely weighted integrability as
input, without a uniform bound on the normalized input. -/
theorem actualTransport_mass_of_weighted_integrable (hj : j ≤ N)
    {F : Config G (C.side j p) → E}
    (hF : Integrable (fun U => (C.path.rep N p j).eval U • F U) (prior G _))
    (hm : m ≤ j) :
    (∫ U, (C.path.rep N p m).eval U • actualTransport C (N := N) F hm U
      ∂prior G _) = ∫ U, (C.path.rep N p j).eval U • F U ∂prior G _ := by
  simp_rw [actualTransport_unnormalize C hC hj]
  exact gust_sum C.path N p j _ hF hm

/-- Native normalized scalar readout is preserved through every actual
intermediate level on the same family, cutoff and period. -/
theorem actualScene_transport (hj : j ≤ N)
    {F : Config G (C.side j p) → E}
    (hF : Integrable (fun U => (C.path.rep N p j).eval U • F U) (prior G _))
    (hm : m ≤ j) :
    (∫ U, actualTransport C (N := N) F hm U ∂scene C.path N p m) =
      ∫ U, F U ∂scene C.path N p j := by
  rw [actualScene_formula C hC (hm.trans hj), actualScene_formula C hC hj,
    actualTransport_mass_of_weighted_integrable C hC hj hF hm]

/-- A finite collection of errors born at different actual levels has the
same total scalar readout after transport to any common earlier level. -/
theorem actualScene_sumTransport {ι : Type*} [Fintype ι]
    (level : ι → ℕ) (hj : ∀ i, level i ≤ N) (hm : ∀ i, m ≤ level i)
    (F : ∀ i, Config G (C.side (level i) p) → E)
    (hF : ∀ i, Integrable
      (fun U => (C.path.rep N p (level i)).eval U • F i U) (prior G _)) :
    (∫ U, ∑ i, actualTransport C (N := N) (F i) (hm i) U
      ∂scene C.path N p m) =
      ∑ i, ∫ U, F i U ∂scene C.path N p (level i) := by
  rw [integral_finsetSum]
  · simp_rw [actualScene_transport C hC (hj _) (hF _) (hm _)]
  · intro i _
    exact actualScene_integrable_of_weighted C hC ((hm i).trans (hj i))
      (actualTransport_weighted_integrable_of_integrable C hC (hj i) (hF i) (hm i))

/-- Existing integrated scalar prices add once; no depth-dependent
normalization factor or pointwise forced-density bound is introduced. -/
theorem actualScene_sumTransport_norm_le {ι : Type*} [Fintype ι]
    (level : ι → ℕ) (hj : ∀ i, level i ≤ N) (hm : ∀ i, m ≤ level i)
    (F : ∀ i, Config G (C.side (level i) p) → E)
    (hF : ∀ i, Integrable
      (fun U => (C.path.rep N p (level i)).eval U • F i U) (prior G _))
    (δ : ι → ℝ)
    (hδ : ∀ i, ‖∫ U, F i U ∂scene C.path N p (level i)‖ ≤ δ i) :
    ‖∫ U, ∑ i, actualTransport C (N := N) (F i) (hm i) U
      ∂scene C.path N p m‖ ≤ ∑ i, δ i := by
  rw [actualScene_sumTransport C hC level hj hm F hF]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hδ i)

/-- The integrated error of one actual conditional step is exactly the
difference of its two native scalar readouts. -/
theorem actualScene_step_error (hm : m < N)
    {F : Config G (C.side m p) → E}
    {H : Config G (C.side (m+1) p) → E}
    (hF : Integrable (fun U => (C.path.rep N p m).eval U • F U) (prior G _))
    (hH : Integrable (fun U => (C.path.rep N p (m+1)).eval U • H U) (prior G _)) :
    (∫ U, F U - actualAverage C (N := N) H U ∂scene C.path N p m) =
      (∫ U, F U ∂scene C.path N p m) -
        ∫ U, H U ∂scene C.path N p (m+1) := by
  have he : actualTransport C (N := N) H (Nat.le_succ m) =
      actualAverage C (N := N) H := by
    rw [actualTransport_step C hC hm H (Nat.lt_succ_self m),
      actualTransport_base C hC hm]
  rw [← he, integral_sub (actualScene_integrable_of_weighted C hC hm.le hF)
    (actualScene_integrable_of_weighted C hC hm.le
      (actualTransport_weighted_integrable_of_integrable C hC hm hH (Nat.le_succ m))),
    actualScene_transport C hC hm hH (Nat.le_succ m)]

/-- A finite interval of genuine local scalar-error receipts controls the
two endpoint readouts on exactly the same actual history. This is an
assembly theorem: it does not supply the local reader estimates. -/
theorem actualScene_error_accumulation (hj : j ≤ N) (hm : m ≤ j)
    (F : ∀ i, Config G (C.side i p) → E) (δ : ℕ → ℝ)
    (hF : ∀ i, m ≤ i → i ≤ j → Integrable
      (fun U => (C.path.rep N p i).eval U • F i U) (prior G _))
    (hδ : ∀ i, m ≤ i → i < j →
      ‖∫ U, F i U - actualAverage C (N := N) (F (i+1)) U
        ∂scene C.path N p i‖ ≤ δ i) :
    ‖(∫ U, F m U ∂scene C.path N p m) -
      ∫ U, F j U ∂scene C.path N p j‖ ≤ ∑ i ∈ Finset.Ico m j, δ i := by
  induction hm using Nat.decreasingInduction with
  | self => simp
  | of_succ l hl ih =>
    have hstep := hδ l le_rfl hl
    rw [actualScene_step_error C hC (hl.trans_le hj)
      (hF l le_rfl hl.le) (hF (l+1) (Nat.le_succ l) hl)] at hstep
    have hrest := ih
      (fun i hi hij => hF i ((Nat.le_succ l).trans hi) hij)
      (fun i hi hij => hδ i ((Nat.le_succ l).trans hi) hij)
    calc
      _ ≤ ‖(∫ U, F l U ∂scene C.path N p l) -
          ∫ U, F (l+1) U ∂scene C.path N p (l+1)‖ +
          ‖(∫ U, F (l+1) U ∂scene C.path N p (l+1)) -
          ∫ U, F j U ∂scene C.path N p j‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ l + ∑ i ∈ Finset.Ico (l+1) j, δ i := add_le_add hstep hrest
      _ = _ := (Finset.sum_eq_sum_Ico_succ_bot hl δ).symm

omit [CompleteSpace E] in
/-- A raw numerator L1 price measured against the actual partition produces
both integrability and the native scalar readout bound. The estimate on the
numerator is an explicit input, not a pointwise bound on the vacuum inverse. -/
theorem actualScene_norm_le_of_rawL1 (hj : j ≤ N)
    {F : Config G (C.side j p) → E}
    (hF : Integrable (fun U => (C.path.rep N p j).eval U • F U) (prior G _))
    {δ : ℝ}
    (hδ : (∫ U, ‖(C.path.rep N p j).eval U • F U‖ ∂prior G _) ≤
      partition G (C.side N p) (C.path.β N p N) * δ) :
    Integrable F (scene C.path N p j) ∧
      ‖∫ U, F U ∂scene C.path N p j‖ ≤ δ := by
  refine ⟨actualScene_integrable_of_weighted C hC hj hF, ?_⟩
  have hZ := (Wilson.partition_pos (G := G) (n := C.side N p) (C.path.β N p N))
  rw [actualScene_formula C hC hj, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hZ.le)]
  calc
    _ ≤ (partition G (C.side N p) (C.path.β N p N))⁻¹ *
        ∫ U, ‖(C.path.rep N p j).eval U • F U‖ ∂prior G _ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (inv_nonneg.mpr hZ.le)
    _ ≤ (partition G (C.side N p) (C.path.β N p N))⁻¹ *
        (partition G (C.side N p) (C.path.β N p N) * δ) :=
      mul_le_mul_of_nonneg_left hδ (inv_nonneg.mpr hZ.le)
    _ = δ := by rw [← mul_assoc, inv_mul_cancel₀ hZ.ne', one_mul]

omit [CompleteSpace E] in
/-- Undo the actual vacuum in a one-step error while retaining the original
physical transition and its incoming coupling. -/
theorem actualStepNumerator (hm : m < N)
    (F : Config G (C.side m p) → E) (H : Config G (C.side (m+1) p) → E)
    (V : Config G (C.side m p)) :
    (C.path.rep N p m).eval V • (F V - actualAverage C (N := N) H V) =
      (C.path.rep N p m).eval V • F V -
        (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
          (fun U => (C.path.rep N p (m+1)).eval U • H U) V := by
  rw [smul_sub, actualAverage_push, smul_smul,
    mul_inv_cancel₀ (Multi.AxisShift.chosen_positive hC.wilson hm.le V).ne', one_smul]

omit [CompleteSpace E] in
/-- A genuine L1 estimate on the complete one-step numerator is a sufficient
scalar-error receipt, with no independent lower bound on the vacuum. -/
theorem actualScene_step_norm_le_of_rawL1 (hm : m < N)
    {F : Config G (C.side m p) → E}
    {H : Config G (C.side (m+1) p) → E}
    (hF : Integrable (fun U => (C.path.rep N p m).eval U • F U) (prior G _))
    (hH : Integrable (fun U => (C.path.rep N p (m+1)).eval U • H U) (prior G _))
    {δ : ℝ}
    (hδ : (∫ V, ‖(C.path.rep N p m).eval V • F V -
      (C.path.levels.clock.op m p).push (C.path.β N p (m+1))
        (fun U => (C.path.rep N p (m+1)).eval U • H U) V‖ ∂prior G _) ≤
      partition G (C.side N p) (C.path.β N p N) * δ) :
    Integrable (fun U => F U - actualAverage C (N := N) H U) (scene C.path N p m) ∧
      ‖∫ U, F U - actualAverage C (N := N) H U ∂scene C.path N p m‖ ≤ δ := by
  have he : actualTransport C (N := N) H (Nat.le_succ m) =
      actualAverage C (N := N) H := by
    rw [actualTransport_step C hC hm H (Nat.lt_succ_self m),
      actualTransport_base C hC hm]
  have hA := actualTransport_weighted_integrable_of_integrable C hC hm hH (Nat.le_succ m)
  rw [he] at hA
  have hres : Integrable (fun U => (C.path.rep N p m).eval U •
      (F U - actualAverage C (N := N) H U)) (prior G _) := by
    exact (hF.sub hA).congr (ae_of_all _ fun U => (smul_sub _ _ _).symm)
  apply actualScene_norm_le_of_rawL1 C hC hm.le hres
  simpa only [actualStepNumerator C hC hm] using hδ

/-- Full finite scalar-error propagation directly from genuine actual raw
numerator prices. All local prices use the same fixed-cutoff partition. -/
theorem actualScene_error_accumulation_of_rawL1 (hj : j ≤ N) (hm : m ≤ j)
    (F : ∀ i, Config G (C.side i p) → E) (δ : ℕ → ℝ)
    (hF : ∀ i, m ≤ i → i ≤ j → Integrable
      (fun U => (C.path.rep N p i).eval U • F i U) (prior G _))
    (hδ : ∀ i, m ≤ i → i < j →
      (∫ V, ‖(C.path.rep N p i).eval V • F i V -
        (C.path.levels.clock.op i p).push (C.path.β N p (i+1))
          (fun U => (C.path.rep N p (i+1)).eval U • F (i+1) U) V‖ ∂prior G _) ≤
        partition G (C.side N p) (C.path.β N p N) * δ i) :
    ‖(∫ U, F m U ∂scene C.path N p m) -
      ∫ U, F j U ∂scene C.path N p j‖ ≤ ∑ i ∈ Finset.Ico m j, δ i := by
  apply actualScene_error_accumulation C hC hj hm F δ hF
  intro i hmi hij
  exact (actualScene_step_norm_le_of_rawL1 C hC (hij.trans_le hj)
    (hF i hmi hij.le) (hF (i+1) (hmi.trans (Nat.le_succ i)) hij) (hδ i hmi hij)).2

end YM.Integration
