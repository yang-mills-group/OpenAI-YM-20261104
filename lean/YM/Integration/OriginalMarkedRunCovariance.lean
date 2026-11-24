import YM.Integration.OriginalMarkedRunAction
import YM.Integration.ActualRunCoarseReadout

/-! Exact signed covariance after vacuum normalization of the positive
physical action and its funded approximation on the original Run. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.OriginalMarkedRunCovariance
open Function Filter MeasureTheory Lattice RG Wilson RG.Supply Pressure Extra.Histories
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato ConnectedActivityE6.Blaze.Thermal1020
open ConnectedActivityE6.Blaze.Thermal1020.Shared GapsLocal.Renew OriginalMarkedRunAction
open scoped BigOperators Classical
variable {G : Gauge} {n : Side}

def mass (P : Rep G n) : ℝ := ∫ U, P.eval U ∂prior G n

def mean (P : Rep G n) (f : Config G n → ℂ) : ℂ :=
  (mass P : ℂ)⁻¹ * ∫ U, (P.eval U : ℂ) * f U ∂prior G n

def covariance (P : Rep G n) (f w : Config G n → ℂ) : ℂ :=
  mean P (fun U => w U * f U) - mean P f * mean P w

variable (R : Run G) {N p m d : ℕ} (hm : m<N)
local notation "S" => ActualRunSpring.selected R N p m hm
local notation "out" => R.family.path.rep N p m
local notation "keep" => approximation R (p:=p) hm d
local notation "B" => R.alloy.B.a.budget m
local notation "Z" => partition G (R.family.side N p) (R.family.beta N p)

def weight (R : Run G) {N p m : ℕ} (hm : m<N) (d : ℕ)
    (U : Config G (R.family.side m p)) : ℝ :=
  Real.exp (-(remainder R (p:=p) hm d).additive (R.alloy.B.a.budget m) U)

local notation "w" => fun U : Config G (R.family.side m p) => (weight R hm d U : ℂ)

theorem factor (A : Comparison R (p:=p) hm d) (U : Config G (R.family.side m p)) :
    (out).eval U = (keep).eval U * weight R hm d U := by
  rw [(S).coarse]
  exact A.posterior.matters U

theorem keep_positive (A : Comparison R (p:=p) hm d) (U : Config G (R.family.side m p)) :
    0 < (keep).eval U := by
  have h := Multi.AxisShift.chosen_positive (H:=R.family.path) R.makes.wilson hm.le U
  rw [show (R.family.path.rep N p m).eval U = _ from factor R hm A U] at h
  exact pos_of_mul_pos_left h (Real.exp_pos _).le

theorem keep_envelope (A : Comparison R (p:=p) hm d) : Envelope (keep).eval := by
  apply Rep.envelope
  constructor
  · rw [A.path,A.clip]
    exact (R.makes.wilson.represents N p m hm.le).good.paths
  · rw [show (keep).p = B from A.posterior.volume.symm]
    exact A.posterior.fit

private theorem positive_mass_on_prior (P : Rep G n) (env : Envelope P.eval)
    (pos : ∀ U, 0 < P.eval U) : 0 < mass P := by
  apply (integral_pos_iff_support_of_nonneg (fun U => (pos U).le)
    (env.integrable (prior G n))).mpr
  have hs : Function.support P.eval = Set.univ := Set.eq_univ_of_forall fun U => (pos U).ne'
  simp [hs]

theorem mass_positive (A : Comparison R (p:=p) hm d) : 0 < mass keep :=
  positive_mass_on_prior (n:=R.family.side m p) (keep) (keep_envelope R hm A) (keep_positive R hm A)

theorem mean_one (A : Comparison R (p:=p) hm d) : mean keep 1 = 1 := by
  unfold mean
  simp only [Pi.one_apply,mul_one]
  rw [integral_complex_ofReal]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (mass_positive R hm A).ne')

include hm in
theorem actual_mean (f : Config G (R.family.side m p) → ℂ) :
    ActualRunCoarseReadout.expectation R N p m f = mean out f := by
  unfold mean mass ActualRunCoarseReadout.expectation ActualRunCoarseReadout.readout
  rw [(ActualCoveredNormalization.same_run_reference R N p m hm.le).2.2]

theorem bounded {P : Rep G n} (finite : Integrable P.eval (prior G n))
    (nonnegative : ∀ U, 0 ≤ P.eval U) (positive : 0 < mass P)
    (f : Config G n → ℂ) (b : ℝ) (bound : ∀ U, ‖f U‖ ≤ b) : ‖mean P f‖ ≤ b := by
  have estimate : ‖∫ U, (P.eval U : ℂ)*f U ∂prior G n‖ ≤ mass P*b := by
    unfold mass
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le (finite.mul_const b)
    refine ae_of_all _ fun U => ?_
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (nonnegative U)]
    exact mul_le_mul_of_nonneg_left (bound U) (nonnegative U)
  unfold mean
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  exact (mul_le_mul_of_nonneg_left estimate (inv_nonneg.mpr positive.le)).trans_eq
    (by rw [← mul_assoc,inv_mul_cancel₀ positive.ne',one_mul])

private theorem weighted_vacuum (A : Comparison R (p:=p) hm d) :
    mean keep (w) = (mass keep : ℂ)⁻¹ * (Z : ℂ) := by
  unfold mean
  congr 1
  calc ∫ U, ((keep).eval U : ℂ) * (weight R hm d U : ℂ) ∂prior G (R.family.side m p) =
        ∫ U, ((out).eval U : ℂ) ∂prior G (R.family.side m p) := by
          apply integral_congr_ae
          refine Eventually.of_forall fun U => ?_
          change (((keep).eval U : ℂ) * (weight R hm d U : ℂ)) = ((out).eval U : ℂ)
          rw [← Complex.ofReal_mul]
          exact congrArg Complex.ofReal (factor R hm A U).symm
       _ = _ := by
         rw [integral_complex_ofReal,(ActualCoveredNormalization.same_run_reference R N p m hm.le).2.2]

theorem vacuum_ne_zero (A : Comparison R (p:=p) hm d) : mean keep (w) ≠ 0 := by
  rw [weighted_vacuum R hm A]
  exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr (mass_positive R hm A).ne'))
    (Complex.ofReal_ne_zero.mpr (partition_pos _).ne')

private theorem scalar_ratio (a z t : ℂ) (ha : a ≠ 0) (hz : z ≠ 0) :
    z⁻¹ * t = (a⁻¹ * t) / (a⁻¹ * z) := by
  field_simp [ha, hz]

theorem ratio (A : Comparison R (p:=p) hm d) (f : Config G (R.family.side m p) → ℂ) :
    ActualRunCoarseReadout.expectation R N p m f =
      mean keep (fun U => (weight R hm d U : ℂ) * f U) / mean keep (w) := by
  rw [weighted_vacuum R hm A]
  unfold mean ActualRunCoarseReadout.expectation ActualRunCoarseReadout.readout
  have tilt : (∫ U, ((keep).eval U:ℂ) * ((weight R hm d U:ℂ) * f U) ∂prior G (R.family.side m p)) =
      ∫ U, ((out).eval U:ℂ) * f U ∂prior G (R.family.side m p) := by
    apply integral_congr_ae
    refine Eventually.of_forall fun U => ?_
    change ((keep).eval U : ℂ) * ((weight R hm d U : ℂ) * f U) = ((out).eval U : ℂ) * f U
    rw [← mul_assoc,← Complex.ofReal_mul,← factor R hm A U]
  exact (congrArg ((Z:ℂ)⁻¹ * ·) tilt.symm).trans (scalar_ratio _ _ _
    (Complex.ofReal_ne_zero.mpr (mass_positive R hm A).ne')
    (Complex.ofReal_ne_zero.mpr (partition_pos _).ne'))

/-- Both means use the proper physical normalization. The discrepancy
retains only the covariance with the omitted ordinary action. -/
theorem residual (A : Comparison R (p:=p) hm d) (f : Config G (R.family.side m p) → ℂ) :
    ActualRunCoarseReadout.expectation R N p m f - mean keep f =
      covariance keep f (w) / mean keep (w) := by
  rw [ratio R hm A f]
  unfold covariance
  field_simp [vacuum_ne_zero R hm A]

/-- A single purchased Run answers every signed subproduct at every
period and upper cutoff after the same stage threshold for that order. -/
theorem marked {ι : Type*} (hG : G.Simple)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (fee : Mallow.RG12.Earned (checkout G) R.kit.shape R.alloy.delay) (d : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ) (hm : m<N) (s : Finset ι)
      (fields : ι → Config G (R.family.side m p) → ℂ),
      let f := fun U => ∏ i ∈ s, fields i U
      let P := approximation R (p:=p) hm d
      let z := fun U : Config G (R.family.side m p) => (weight R hm d U : ℂ)
      ActualRunCoarseReadout.expectation R N p m f - mean P f =
        covariance P f z / mean P z := by
  filter_upwards [calendar R hG marks fee d] with m paid N p hm s fields
  exact residual R hm (paid N p hm) _

end YM.Integration.OriginalMarkedRunCovariance
