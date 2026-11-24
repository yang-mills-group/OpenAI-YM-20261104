import YM.Integration.ActualOuterQuarterProfile
import YM.MS.Dial.Set
import YM.Push.STRESS_FLUX.Matching
import YM.FullVolume.Cross

/-! The literal right-ceil offsets on a relative mesh. The point configuration
is the normalized local coefficient configuration; fixed physical exterior
points are not silently rescaled into it. Shape and separation bounds are
explicit geometric inputs. The actual schedule, coarse side, quarter-period
head, and mesh-then-period filter are retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRelativeProfileTrial

open Filter Lattice
open PhysicalNext.Repeat.Legato
open scoped Topology Classical

variable {I : Type} {n : ℕ}

def offsets (θ : I → ℝ) (z : I → Fin n → MS.Tone.QP)
    (i : Fin n) (a : I) : Cover :=
  fun j => ⌈z a i j / Real.exp (-θ a)⌉

def sampled (θ : I → ℝ) (z : I → Fin n → MS.Tone.QP)
    (a : I) (i : Fin n) : MS.Tone.QP :=
  Real.exp (-θ a) • MS.Tone.embed (offsets θ z i a)

/-- The native right-ceil convention has error at most one relative mesh. -/
theorem rounding_error (θ : I → ℝ) (z : I → Fin n → MS.Tone.QP)
    (a : I) (i : Fin n) :
    ‖sampled θ z a i - z a i‖ ≤ Real.exp (-θ a) := by
  apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2
  intro j
  let t := Real.exp (-θ a)
  have ht : 0 < t := Real.exp_pos _
  have hlo := mul_le_mul_of_nonneg_left (Int.le_ceil (z a i j / t)) ht.le
  have hhi := mul_lt_mul_of_pos_left (Int.ceil_lt_add_one (z a i j / t)) ht
  have he : t * (z a i j / t) = z a i j := by field_simp [ht.ne']
  change |t * (⌈z a i j / t⌉ : ℝ) - z a i j| ≤ t
  rw [abs_le]
  constructor <;> nlinarith

private theorem scale_norm (θ : ℝ) (v : MS.Tone.QP) :
    ‖v‖ = Real.exp θ * ‖Real.exp (-θ) • v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← mul_assoc,
    ← Real.exp_add]
  simp

private theorem sampled_bound (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a)
    (z : I → Fin n → MS.Tone.QP) (K : ℝ)
    (hz : ∀ a i, ‖z a i‖ ≤ K) (a : I) (i : Fin n) :
    ‖sampled θ z a i‖ ≤ K + 1 := by
  have he := rounding_error θ z a i
  have ht : Real.exp (-θ a) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hθ a))
  have hn : ‖sampled θ z a i‖ ≤ ‖sampled θ z a i - z a i‖ + ‖z a i‖ := by
    simpa using norm_add_le (sampled θ z a i - z a i) (z a i)
  linarith [hz a i]

private theorem offset_bound (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a)
    (z : I → Fin n → MS.Tone.QP) (K : ℝ)
    (hz : ∀ a i, ‖z a i‖ ≤ K) (a : I) (i : Fin n) :
    ‖MS.Tone.embed (offsets θ z i a)‖ ≤ (K + 1) * Real.exp (θ a) := by
  rw [scale_norm (θ a)]
  exact (mul_le_mul_of_nonneg_left (sampled_bound θ hθ z K hz a i)
    (Real.exp_pos _).le).trans_eq (mul_comm _ _)

variable {G : Gauge}

def trial (R : Run G) (level : I → ℕ) (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a)
    (μ : ℝ) (z : I → Fin n → MS.Tone.QP) :
    MS.Dial.Trial (ActualOuterQuarterProfile.Cutoffs I) (Fin n) where
  profile := ActualOuterQuarterProfile.profile θ hθ μ
  side := ActualOuterQuarterProfile.lengths R.family.S level
  off i w := offsets θ z i w.1
  head w := ActualCoarseQuarterProfile.head R.family.S (level w.1) w.2.2

/-- The relative sampling profile is built from explicit bounded positions. -/
theorem total (R : Run G) (level : I → ℕ) (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a)
    (μ : ℝ) (z : I → Fin n → MS.Tone.QP) (K : ℝ) (hK : 0 ≤ K)
    (hz : ∀ a i, ‖z a i‖ ≤ K) :
    MS.Tide.Profile (trial R level θ hθ μ z).profile (trial R level θ hθ μ z).off := by
  intro i
  refine ⟨K + 1, by linarith, fun w => ?_⟩
  exact offset_bound θ hθ z K hz w.1 i

/-- Uniform separation survives the literal right-ceil operation. -/
theorem mesh (R : Run G) (level : I → ℕ) (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a)
    (μ : ℝ) (z : I → Fin n → MS.Tone.QP) (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η)
    (hz : ∀ a i, ‖z a i‖ ≤ K)
    (hsep : ∀ a i j, i ≠ j → η ≤ ‖z a i - z a j‖)
    (hsmall : ∀ a, 4 * Real.exp (-θ a) ≤ η) :
    MS.Rake.Mesh (trial R level θ hθ μ z).profile
      (MS.Fleet.info (trial R level θ hθ μ z).off) := by
  intro i j hij
  constructor
  · refine ⟨2 * (K + 1), by positivity, fun w => ?_⟩
    change ‖MS.Tone.embed (offsets θ z i w.1) - MS.Tone.embed (offsets θ z j w.1)‖ ≤ _
    have hi := offset_bound θ hθ z K hz w.1 i
    have hj := offset_bound θ hθ z K hz w.1 j
    have h := norm_sub_le (MS.Tone.embed (offsets θ z i w.1))
      (MS.Tone.embed (offsets θ z j w.1))
    change _ ≤ 2 * (K + 1) * Real.exp (θ w.1)
    linarith
  · refine ⟨η / 2, by positivity, fun w => ?_⟩
    have hi := rounding_error θ z w.1 i
    have hj := rounding_error θ z w.1 j
    have hd : ‖z w.1 i - z w.1 j‖ ≤
        ‖sampled θ z w.1 i - sampled θ z w.1 j‖ +
        ‖sampled θ z w.1 i - z w.1 i‖ + ‖sampled θ z w.1 j - z w.1 j‖ := by
      calc
        _ = ‖(sampled θ z w.1 i - sampled θ z w.1 j) -
            (sampled θ z w.1 i - z w.1 i) + (sampled θ z w.1 j - z w.1 j)‖ := by
              congr 1; abel
        _ ≤ ‖(sampled θ z w.1 i - sampled θ z w.1 j) -
            (sampled θ z w.1 i - z w.1 i)‖ + ‖sampled θ z w.1 j - z w.1 j‖ := norm_add_le _ _
        _ ≤ _ := add_le_add_left (norm_sub_le _ _) _
    have hs : η / 2 ≤ ‖sampled θ z w.1 i - sampled θ z w.1 j‖ := by
      linarith [hsep w.1 i j hij, hsmall w.1]
    change η / 2 * Real.exp (θ w.1) ≤
      ‖MS.Tone.embed (offsets θ z i w.1) - MS.Tone.embed (offsets θ z j w.1)‖
    rw [scale_norm (θ w.1)]
    rw [smul_sub]
    exact (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le).trans_eq'
      (mul_comm _ _)

/-- Native Uses for the actual coarse side and ordered original regulator filter.
The hypotheses are the displayed local shape bounds, not an assumed Uses predicate. -/
theorem uses (R : Run G) (l : Filter I) (f : Extraction.Order) (level : I → ℕ)
    (θ : I → ℝ) (hθ : ∀ a, 0 ≤ θ a) (hdiv : Tendsto θ l atTop)
    (μ : ℝ) (z : I → Fin n → MS.Tone.QP) (K η : ℝ) (hK : 0 ≤ K) (hη : 0 < η)
    (hz : ∀ a i, ‖z a i‖ ≤ K)
    (hsep : ∀ a i j, i ≠ j → η ≤ ‖z a i - z a j‖)
    (hsmall : ∀ a, 4 * Real.exp (-θ a) ≤ η) :
    MS.Dial.Uses (trial R level θ hθ μ z) (ActualOuterQuarterProfile.nested l f) μ := by
  refine ⟨total R level θ hθ μ z K hK hz,
    mesh R level θ hθ μ z K η hK hη hz hsep hsmall, fun _ => rfl,
    ActualOuterQuarterProfile.theta_tendsto l f θ hdiv,
    ActualOuterQuarterProfile.super R.family.S l f level θ, ?_, ?_⟩
  · intro w b
    exact ActualCoarseQuarterProfile.clearance R.family.S (level w.1, w.2) b
  · obtain ⟨C, hC, hc⟩ := ActualCoarseQuarterProfile.width R.family.S
    exact ⟨C, hC, fun w => hc (level w.1, w.2)⟩

/-- With the actual relative-scale identity, these are exactly the original
coarse right-ceil sites; the common quarter-period head is kept separately. -/
theorem wrapped_actual (R : Run G) (level : I → ℕ) (θ radius : I → ℝ)
    (x : I → Fin n → E4) (a : I) (i : Fin n) (p : ℕ)
    (hr : radius a ≠ 0) (hscale : Real.exp (θ a) = radius a / R.family.S.a (level a)) :
    wrap (R.family.side (level a) p)
      (offsets θ (fun a i j => x a i j / radius a) i a) =
      StressFlux.Matching.ceilSite R.family (level a) p (x a i) := by
  apply congrArg (wrap (R.family.side (level a) p))
  funext j
  unfold offsets
  congr 1
  rw [Real.exp_neg, hscale]
  field_simp [hr, (R.family.S.a_pos (level a)).ne']

end YM.Integration.ActualRelativeProfileTrial
end
