import YM.Integration.ActualRunRatioGrowth

/-! The original Run's purchased block bound gives a three-halves comparison
of adjacent hatted inverse temperatures. The event precedes every cutoff and
period. No additional post-length payment or Attached premise is required. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunAdjacentHatBeta
open Filter RG PhysicalNext.Repeat.Legato
open scoped Topology

/-- The same original hatted clock grows by at most a factor of three halves
at all sufficiently late stages. -/
theorem three_halves {G : Gauge} (R : Run G) (hG : G.Simple) :
    ∀ᶠ m : ℕ in atTop, R.alloy.B.a.clock.hatBeta (m+1) ≤
      (3/2:ℝ)*R.alloy.B.a.clock.hatBeta m := by
  let A := R.alloy.B.a
  have hbound := (Real.isLittleO_log_id_atTop.const_mul_left G.slopeConstant).bound
    (show 0<(1/3:ℝ) by norm_num)
  have ht := (WardBin.bell A hG).comp (tendsto_add_atTop_nat 1)
  filter_upwards [ht.eventually hbound] with m hm
  have hp := WardBin.hot A (m+1)
  have hL : 0<((A.S.block m).val:ℝ) := by exact_mod_cast (A.S.block m).property
  have hLB : ((A.S.block m).val:ℝ) ≤ A.clock.hatBeta (m+1) := by
    simpa only [Nat.zero_add,pow_one] using
      ActualRunRatioGrowth.ratio_power_le R hG m 0 (Nat.zero_le _)
  have hm' : |G.slopeConstant*Real.log (A.clock.hatBeta (m+1))| ≤
      (1/3:ℝ)*|A.clock.hatBeta (m+1)| := by
    simpa only [Real.norm_eq_abs, id_eq, Function.comp_apply] using hm
  have hs : G.slopeConstant*Real.log ((A.S.block m).val:ℝ) ≤
      A.clock.hatBeta (m+1)/3 := by
    calc
      _ ≤ G.slopeConstant*Real.log (A.clock.hatBeta (m+1)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log hL hLB) (G.slopeConstant_pos hG).le
      _ ≤ |G.slopeConstant*Real.log (A.clock.hatBeta (m+1))| := le_abs_self _
      _ ≤ (1/3:ℝ)*|A.clock.hatBeta (m+1)| := hm'
      _ = _ := by rw [abs_of_pos hp]; ring
  have he := Push.PriceCompiler.beta_eq R.alloy.B.valid m
  rw [← Push.PriceCompiler.block_eq R.alloy.B.valid m] at he
  change A.clock.hatBeta (m+1)=A.clock.hatBeta m+
    G.slopeConstant*Real.log ((A.S.block m).val:ℝ) at he
  change A.clock.hatBeta (m+1)≤(3/2:ℝ)*A.clock.hatBeta m
  linarith

end YM.Integration.ActualRunAdjacentHatBeta
end
