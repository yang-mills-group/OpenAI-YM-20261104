import YM.Gaps1020.Local.Expressed
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.FVA1
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera Mallow
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
open Next.Foundations Extra.Histories YM.Planned.GuardedAtom
section charges
open Blush ConnectedActivityE6.Blaze.Thermal1020
variable {L:Side}{t : ℝ}(ht:0<t)
include ht
/-- Seed factor vs any prescribed number of same-scale forced divisors.
Strengthens Blush.efferv to pay repeated mask alignment mergers. -/
lemma forfeit (b:ℝ)(n:ℕ): Rate G L b (fun x=> (glyph x)⁻¹^n * straw t L G x):=by
  refine (infuso L 2 (t/4) _ (by positivity) (by norm_num: (0:ℝ)<1/8) b).compare ?_
  have hg:= Delay.monitor_pays G L 0 (hD:=(show (0:ℝ) ≤ 64/t * n from by positivity)) (show (0:ℝ)<1 by norm_num)
  filter_upwards [eventually_gt_atTop (Real.exp 1), hg] with x hx hh
  let V:= Delay.fineMonitor G L x; let u:=Real.exp ((Real.log (Real.log x))^2)
  have hz : 0≤ Real.log (Real.log x) := Real.log_nonneg ((by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hx.le))
  have hV : x≤ betaF G x L:=le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have hU : u ≤ V:=by
    apply Real.exp_monotone; apply pow_le_pow_left₀ hz _; have he : 1 < x:= lt_trans (Real.one_lt_exp_iff.mpr zero_lt_one) hx; exact Real.log_le_log (Real.log_pos he) (Real.log_le_log (by linarith) hV)
  have hp : 64/t * n ≤ V :=by simpa using hh
  have hu : u ^ ((1:ℝ)/5) ≤ u := (Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) (show (1:ℝ)/5≤1 by norm_num)).trans_eq (Real.rpow_one _)
  unfold straw lauge; rw [abs_of_pos (mul_pos (pow_pos (inv_pos.mpr (glyphpos _)) _) (mul_pos zero_lt_two (Real.exp_pos _))), abs_of_pos (mul_pos zero_lt_two (Real.exp_pos _)),mul_left_comm]; apply mul_le_mul_of_nonneg_left _ zero_le_two; unfold Blush.glyph; rw [Real.sqrt_eq_rpow,← Real.exp_mul, ← Real.exp_neg, ← Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_le_exp.mpr
  change (n:ℝ) * -( -(u^((1:ℝ)/5))*(1/2))+-(t/4)*(1/4)*V^2 ≤ -(t/4)*(1/8)*V^2
  have hT:0<V:=Real.exp_pos _
  rw [div_mul_eq_mul_div, div_le_iff₀ ht] at hp
  have hp':= mul_le_mul_of_nonneg_right hp hT.le
  have hk:= mul_le_mul_of_nonneg_left (hu.trans hU) (show 0≤ (n:ℝ) by positivity)
  nlinarith
end charges
open Blush ConnectedActivityE6.Blaze.Thermal1020
open RG12 Daisy.Charity.RG12
/-- Enough for countably many fixed (not moving) precision/attachment requests
on the same assembly. Uses the same true calendar under each delay; the K suppression
is at aligned output threshold and unreweighted marker radii. -/
def garrison (G:Gauge) : Daisy.Charity.RG12.Decal G where
  rub _ _ _ L _ t _ _ j x:= ∀ i≤j, (horizonRadius G L x)^i * (glyph x)⁻¹^i * straw t L G x ≤ 1
  good _ _ _:= by
    refine ⟨0,fun L _ _ t _ _ J _ _ ht=>?_⟩
    have hh (i:Fin (J+1)): ∀ᶠ x in atTop, (horizonRadius G L x)^i.val * (glyph x)⁻¹^i.val * straw t L G x ≤ 1:=by
      let y:= Thermal1020.ray*i.val; let f:= horizonRadius G L
      have hp : Rate G L (-1) (fun x=>f x ^(i.val) * ((glyph x)⁻¹^i.val * straw t L G x)):=by
        convert! ((Rate.power (a:=Thermal1020.ray)).pow i.val).mul (forfeit (L:=L) ht (-1-y) i.val) using 1; unfold y; ring
      filter_upwards [hp.below (by norm_num) 1 zero_lt_one] with x hx
      rw [mul_assoc]; exact (le_abs_self _).trans hx
    filter_upwards [Filter.eventually_all.mpr hh] with x hx i hi; exact hx ⟨i,by omega⟩
end YM.PhysicalNext.Repeat.FVA1
