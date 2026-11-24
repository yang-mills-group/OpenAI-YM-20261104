import YM.Integration.WilsonPositionProgramInversion

/-! The original older dates can absorb every fixed power of the reporting logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramInfraredRoom
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler WilsonPositionProgramCommonWindow
open scoped Classical Topology
variable {G : Gauge} (C : Run G) (simple : G.Simple) (D : XSpace.Run)
local notation "A" => C.family.path.levels
local notation "Λ" => RG16.Lambda A
local notation "β" => C.family.path.levels.clock.hatBeta

include simple in
private theorem vanishes (p : ℕ) : Tendsto (fun m => (Λ m)^p / β m) atTop (𝓝 0) := by
  have go : Tendsto Λ atTop atTop := tendsto_atTop_mono
    (f:=WilsonAdmissionScale.logarithm A) (fun m => by
      change Real.log (β m) ≤ 2+Real.log (β m)
      linarith)
    (WilsonAdmissionScale.logarithm_tendsto A simple)
  have small := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero p).comp go
  have priced := (tendsto_const_nhds (x:=Real.exp 2)).mul small
  rw [mul_zero] at priced
  convert priced using 1
  ext m
  have pos := zero_lt_one.trans (C.family.path.levels.fits.delayed m)
  change (Λ m)^p / β m = Real.exp 2 * ((Λ m)^p * Real.exp (-(2+Real.log (β m))))
  rw [neg_add_rev,Real.exp_add,Real.exp_neg,Real.exp_log pos,Real.exp_neg]
  field_simp

include simple in
/-- The starting date and all constants are fixed before the physical ultraviolet and period limits. -/
theorem capacity (start : ℕ) (w : ℕ → ℕ) (stamps : ∀ i, (C.family.S.block (start+i)).val=D.ratio^(w i))
    (K : ℝ) (p : ℕ) : ∀ᶠ n in atTop, K*(Λ (start+n))^p ≤ (elapsed w n : ℝ) := by
  let speed := G.slopeConstant*Real.log D.ratio
  have dr : 1 < (D.ratio : ℝ) := by exact_mod_cast (show 1 < D.ratio from lt_of_lt_of_le (by decide) D.large)
  have vpos : 0 < speed := mul_pos (Gauge.slopeConstant_pos simple) (Real.log_pos dr)
  have shifts : Tendsto (fun n : ℕ => start+n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_left n start) tendsto_id
  have first := (tendsto_const_nhds (x:=K*speed)).mul ((vanishes C simple p).comp shifts)
  rw [mul_zero] at first
  have half : ∀ᶠ n in atTop, (K*speed)*((Λ (start+n))^p/β (start+n)) < 1/2 :=
    first.eventually_lt_const (by norm_num)
  have late := ((Next.Rank.Station.hat_rate A simple).comp shifts).eventually_ge_atTop (2*β start)
  filter_upwards [half,late] with n paid after
  have pos := zero_lt_one.trans (C.family.path.levels.fits.delayed (start+n))
  have debt : K*(Λ (start+n))^p*speed ≤ β (start+n)/2 := by
    rw [←mul_div_assoc] at paid
    have h := (div_lt_iff₀ pos).mp paid
    nlinarith only [h]
  have gain : β (start+n) - β start = (elapsed w n:ℝ) * speed := by
    have steps := WilsonPositionProgramInversion.logged C D start w stamps n
    unfold RG.Calendar.hatBeta speed
    calc _ = G.slopeConstant * (C.family.S.scale (start+n)-C.family.S.scale start) := by ring
         _ = _ := by rw [steps]; ring
  apply (mul_le_mul_iff_left₀ vpos).mp
  change 2*β start ≤ β (start+n) at after
  linarith only [debt,after,gain]

end YM.Integration.WilsonPositionProgramInfraredRoom
end
