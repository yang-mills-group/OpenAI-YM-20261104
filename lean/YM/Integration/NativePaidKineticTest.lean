import Mathlib.Algebra.QuadraticDiscriminant
import YM.UVExt.FlowPrice
import YM.Integration.NativePaidKernelCosts

/-!
# A paid nondegenerate curvature test on the original metric

The inverse row already belongs to the same retained Bed. Its row sum
and Floor.inverse give a coordinate lower bound for the metric quadratic
form, without charging the reciprocal of the arbitrary declared eta.
Yamen's existing collar payment bounds the inverse-row cost by log(hatBeta).

The final reciprocal bound requires an actual test with one curvature
coordinate equal to one. Constructing that test and relating its energy
to a selected Plan coefficient remain explicit consumer duties.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativePaidKineticTest
open Matrix Lattice Laurent RG Precision Stationary Bloch Exterior
open RG08 RG08.Supplies
open scoped BigOperators Classical

/-- A right inverse and a nonnegative symmetric quadratic form suffice. -/
theorem inverse_coordinate {I : Type*} [Fintype I] [DecidableEq I]
    (M B : Matrix I I ℝ) (hs : M.transpose = M)
    (hnn : ∀ v : I → ℝ, 0 ≤ v ⬝ᵥ (M *ᵥ v))
    (hinv : M * B = 1) (b : I) (v : I → ℝ)
    (C : ℝ) (hB : B b b ≤ C) :
    (v b) ^ 2 ≤ C * (v ⬝ᵥ (M *ᵥ v)) := by
  let w := B *ᵥ Pi.single b (1 : ℝ)
  have hw : M *ᵥ w = Pi.single b (1 : ℝ) := by
    dsimp only [w]
    rw [mulVec_mulVec, hinv, one_mulVec]
  have hvw : v ⬝ᵥ (M *ᵥ w) = v b := by
    rw [hw, dotProduct_single, mul_one]
  have hwv : w ⬝ᵥ (M *ᵥ v) = v b := by
    calc
      _ = (M *ᵥ w) ⬝ᵥ v := by
        rw [dotProduct_mulVec, ← mulVec_transpose, hs]
      _ = v b := by rw [hw, single_dotProduct, one_mul]
  have hww : w ⬝ᵥ (M *ᵥ w) = B b b := by
    rw [hw, dotProduct_single, mul_one]
    dsimp only [w]
    rw [mulVec_single_one]
    rfl
  have hp : ∀ t : ℝ,
      0 ≤ (v ⬝ᵥ (M *ᵥ v)) * (t * t) + (2 * v b) * t + B b b := by
    intro t
    have h := hnn (t • v + w)
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, hvw, hwv, hww] at h
    nlinarith only [h]
  have hd := discrim_le_zero hp
  unfold discrim at hd
  have hm := mul_le_mul_of_nonneg_right hB (hnn v)
  nlinarith only [hd, hm]

variable {G : Gauge} {a : Levels G} {H : Horizon a}
  {P X : MapPrices} {Z : ChartRatio G}

/-- The finite type count is explicit and independent of the period. -/
theorem kinetic_coordinate (hH : H.Suffices P)
    (hpaid : Yamen.Payment G P X Z a) (N i : ℕ) (hi : i < N)
    (n : Side) (b : Body 2 n) (v : Body 2 n → ℝ) :
    (v b) ^ 2 ≤
      ((Fintype.card (TypeFace 2) : ℝ) * Real.log (a.clock.hatBeta i)) *
        (v ⬝ᵥ ((H.H N (i + 1)).metric.acts n *ᵥ v)) := by
  let M := (H.H N (i + 1)).metric.acts n
  let B := (H.H N (i + 1)).inverse.acts n
  have hf := hH.all N (i + 1) hi n
  have hnn (u : Body 2 n → ℝ) : 0 ≤ u ⬝ᵥ (M *ᵥ u) := by
    have hu : 0 ≤ u ⬝ᵥ u := Finset.sum_nonneg fun k _ => mul_self_nonneg (u k)
    exact (mul_nonneg (P.eta_pos _).le hu).trans (hf.uniform.1 u).1
  have hr := UVExt.Paths.row_zero (hH.rows N (i + 1) hi).2.2.1
    (P.alpha_pos _).le n
  have hb : ‖B b b‖ ≤ ∑ k, ‖B b k‖ :=
    Finset.single_le_sum (fun k _ => norm_nonneg (B b k)) (Finset.mem_univ b)
  have hdiag : B b b ≤ (Fintype.card (TypeFace 2) : ℝ) * P.Ω (a.clock.J (i + 1)) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hb.trans (hr b))
  have h := inverse_coordinate M B hf.symmetric.1 hnn hf.inverse b v _ hdiag
  have hstamp := Yamen.stamped G P X a.clock.kernel Z (stone a i)
  have hΩ : P.Ω (a.clock.J (i + 1)) ≤ Real.log (a.clock.hatBeta i) :=
    (le_max_right 0 _).trans
      ((hstamp.collar _ le_rfl).trans (Yamen.hatch hpaid i))
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hΩ (Nat.cast_nonneg _)) (hnn v))

/-- A genuine normalized curvature coordinate gives a paid denominator. -/
theorem kinetic_reciprocal (hH : H.Suffices P)
    (hpaid : Yamen.Payment G P X Z a) (N i : ℕ) (hi : i < N)
    (n : Side) (b : Body 2 n) (v : Body 2 n → ℝ) (hv : v b = 1) :
    0 < v ⬝ᵥ ((H.H N (i + 1)).metric.acts n *ᵥ v) ∧
    (v ⬝ᵥ ((H.H N (i + 1)).metric.acts n *ᵥ v))⁻¹ ≤
      (Fintype.card (TypeFace 2) : ℝ) * Real.log (a.clock.hatBeta i) := by
  have h := kinetic_coordinate hH hpaid N i hi n b v
  rw [hv, one_pow] at h
  have hC : 0 ≤ (Fintype.card (TypeFace 2) : ℝ) * Real.log (a.clock.hatBeta i) :=
    mul_nonneg (Nat.cast_nonneg _)
      (zero_le_one.trans (NativePaidKernelCosts.paid_costs hpaid i).1)
  have he : 0 < v ⬝ᵥ ((H.H N (i + 1)).metric.acts n *ᵥ v) := by
    by_contra hn
    have hq := mul_nonpos_of_nonneg_of_nonpos hC (le_of_not_gt hn)
    nlinarith only [h, hq]
  refine ⟨he, ?_⟩
  rw [inv_eq_one_div]
  apply (div_le_iff₀ he).2
  exact h

end YM.Integration.NativePaidKineticTest
end
