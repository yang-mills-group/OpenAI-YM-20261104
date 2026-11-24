import YM.Integration.WilsonPhysicalExteriorMeshStops
import YM.Integration.WilsonDyadicReportingPrice

/-! Count the actual steps to the ultraviolet measuring stop. No abstract
bound on the number of steps or monotonicity of the block sizes is needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalWindowDepth

open Filter Real Lattice RG RG16 Wilson WilsonPhysicalExteriorMeshStops
open PhysicalNext.Repeat.Legato
open scoped Topology

private theorem growth (S : Schedule) (k d : ℕ) :
    (d:ℝ)*log 3 ≤ S.scale (k+d) - S.scale k := by
  induction d with
  | zero => simp
  | succ d ih =>
    have step : log (3:ℝ) ≤ log ((S.block (k+d)).val : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast S.block_large (k+d))
    change ((d+1:ℕ):ℝ)*log 3 ≤ S.scale (k+(d+1)) - S.scale k
    rw [show k+(d+1)=(k+d)+1 by omega,S.scale_succ,Nat.cast_add,Nat.cast_one,add_mul,one_mul]
    linarith

theorem counted {G : Gauge} (R : Run G) (hG : G.Simple)
    (slow : WilsonWindowReportingPace.Slow R.kit) {c : ℝ} (hc : c ≤ 2) :
    ∀ᶠ k : ℕ in atTop, let u := ultraviolet R.family c k
      k < u ∧ ((u-k : ℕ) : ℝ) ≤ (3/log 3) * (Lambda R.family.path.levels k)^2 := by
  have large := (Literal.lambda_leads R.family hG).eventually (eventually_gt_atTop (1:ℝ))
  have window := ultraviolet_window R.family hG slow.2 c
  filter_upwards [large,window] with k hL hw
  let u := ultraviolet R.family c k
  let L := Lambda R.family.path.levels k
  have one : 1 < L := hL
  have two : log (2:ℝ) ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have z : 1 < L + log 2 := by linarith only [one,Real.log_pos (by norm_num : (1:ℝ)<2)]
  have log0 : 0 < log (L+log 2) := Real.log_pos z
  have lw : log (log (L+log 2)) ≤ L+1 := by
    linarith only [Real.log_le_sub_one_of_pos log0,Real.log_le_sub_one_of_pos (by linarith only [z] : 0<L+log 2),two]
  have power : L^c ≤ L^2 := (Real.rpow_le_rpow_of_exponent_le one.le hc).trans_eq (Real.rpow_two _)
  have gap : R.family.S.scale u - R.family.S.scale k ≤ L^c + log (log (L+log 2)) := hw.2.2
  have count := growth R.family.S k (u-k)
  rw [Nat.add_sub_of_le hw.1.le] at count
  refine ⟨hw.1,?_⟩
  change ((u-k:ℕ):ℝ) ≤ (3/log 3) * L^2
  rw [div_mul_eq_mul_div, le_div_iff₀ (Real.log_pos (by norm_num : (1:ℝ)<3))]
  nlinarith [sq_nonneg (L-1)]

end YM.Integration.WilsonPhysicalWindowDepth

