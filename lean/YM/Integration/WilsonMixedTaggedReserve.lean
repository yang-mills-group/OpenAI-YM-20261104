import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! A one-unit connected-support reserve at the original separation B²+1
also pays the fixed-roster inverse marker radii on the short capture interval. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedReserve
open Filter Real
open scoped Topology

/-- B bounds the squared logarithm of the reporting inverse coupling. The
ancestors supporting any mixed word are separated by at least B²+1. -/
theorem quarter (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ x : ℝ in atTop, ∀ B : ℕ, x^2 ≤ B →
      ∃ D : ℕ, D*(4*B+2)+2*B ≤ B^2 ∧
        A*(1+x)*(1+Real.log (2+x)) ≤ D := by
  let κ := (128*(A+1))⁻¹
  have κp : 0 < κ := by unfold κ; positivity
  have grow : Tendsto (fun x:ℝ=>2+x) atTop atTop :=
    Filter.tendsto_atTop_mono (fun x=>by linarith : ∀ x:ℝ, x≤2+x) tendsto_id
  filter_upwards [eventually_ge_atTop (max 16 κ⁻¹),grow.eventually
    (Real.isLittleO_log_id_atTop.def κp)] with x hx fee B hB
  have large : (16:ℝ) ≤ x := (le_max_left ..).trans hx
  have kx : 1 ≤ κ*x := (inv_le_iff_one_le_mul₀' κp).1 ((le_max_right ..).trans hx)
  have x0 : 0 ≤ x := by linarith
  have p : 1 ≤ 2+x := by linarith
  have f : Real.log (2+x) ≤ κ*(2+x) := by
    simpa [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg p),
      abs_of_nonneg (zero_le_one.trans p)] using fee
  have c : 128*κ*(A+1)=1 := by unfold κ; field_simp
  have q : A*(1+x)*(1+Real.log (2+x)) ≤ (6*A*κ)*x^2 := by
    have small : 1+Real.log (2+x) ≤ 3*(κ*x) := by
      calc 1+Real.log (2+x) ≤ κ*x+κ*(2+x) := add_le_add kx f
           _ ≤ 3*(κ*x) := by nlinarith only [mul_le_mul_of_nonneg_left (show 2≤x by linarith) κp.le]
    calc A*(1+x)*(1+Real.log (2+x)) ≤ (A*(2*x))*(3*(κ*x)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hA) small
              (by linarith only [Real.log_nonneg p]) (by positivity)
         _ = _ := by ring
  let D := ⌈x^2/16⌉₊
  have dm : x^2/16 ≤ (D:ℝ) := Nat.le_ceil _
  have dM : (D:ℝ) ≤ x^2/16+1 := (Nat.ceil_lt_add_one (by positivity)).le
  have budget : 8*D+8 ≤ B := by
    have sq : 32 ≤ x^2 := by nlinarith only [large,mul_le_mul_of_nonneg_right large x0]
    have cast : ((8*D+8:ℕ):ℝ) ≤ B := by push_cast; nlinarith only [dM,hB,sq]
    exact_mod_cast cast
  refine ⟨D,?_,q.trans ((mul_le_mul_of_nonneg_right
    (show 6*A*κ ≤ 1/16 by nlinarith only [c,κp.le]) (sq_nonneg x)).trans
      (by nlinarith only [dm]))⟩
  calc D*(4*B+2)+2*B ≤ D*(6*B)+2*B :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
       _ = (6*D+2)*B := by ring
       _ ≤ B*B := Nat.mul_le_mul_right _ (by omega)
       _ = B^2 := by ring

end YM.Integration.WilsonMixedTaggedReserve
