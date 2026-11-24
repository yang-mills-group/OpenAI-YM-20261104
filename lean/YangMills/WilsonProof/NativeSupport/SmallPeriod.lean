import YangMills.WilsonProof.NativeSupport.OriginalPattern

/-! A direct estimate on the actual absolute sum, also at off-calibration
temperatures, whenever the terminal side is bounded by the fixed arity. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.InletSusceptibility.Packet
open Function Finset Lattice RG Wilson RGComparison.Core16
open WilsonUniformUnmarkedInletConnectedCovariance WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder
open scoped Classical BigOperators
variable {G : Gauge} {A : Levels G} {k N per : ℕ}

theorem small_absolute (T : Slices A per) (hk : k ≤ N) (β v : ℕ→ℝ) (r : ℝ)
    {φ : Config G (A.S.side N per)→ℝ} (test : Continuous φ) (sym : GaugeInvariant φ)
    {S : ℝ} (unit : ∀ U,|φ U| ≤ S) {m : ℕ} (side : (A.S.side k per).val ≤ m) :
    let d:=traversal T hk
    ∑ q∈interior d,|picture d β v 1 φ r q| ≤
      (d.depth*((m*scale d)^4*4) : ℕ)*((A.clock.kernel.penalty*2)*(2*S)) := by
  intro d
  have hS := (abs_nonneg _).trans (unit 1)
  have fine : (A.S.side N per).val ≤ m*scale d := (side_scale d).symm.le.trans
    (Nat.mul_le_mul_right _ side)
  have cnt := (count_interior d).trans
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left fine 4)))
  have nn : 0 ≤ (A.clock.kernel.penalty*2)*(2*S) :=
    mul_nonneg (mul_nonneg A.clock.kernel.penalty_pos.le zero_le_two) (mul_nonneg zero_le_two hS)
  calc _ ≤ ∑ _q∈interior d,(A.clock.kernel.penalty*2)*(2*S) := by
            refine sum_le_sum fun q hq=>?_ 
            exact (one_bond d (traversal_ok T hk) β v 1 test sym unit r q).trans_eq
              (congrArg (·*(2*S)) (interior_cap T hk q (mem_filter.mp hq).2.2))
       _ = ((interior d).card:ℝ)*((A.clock.kernel.penalty*2)*(2*S)) := by simp
       _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast cnt) nn


end YM.Integration.InletSusceptibility.Packet
