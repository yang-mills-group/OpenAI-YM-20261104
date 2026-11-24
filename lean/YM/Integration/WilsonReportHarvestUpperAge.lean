import YM.Integration.ActualRunRatioGrowth
import YM.Integration.WilsonReportHarvestSourceReach

/-! The real upper half of the physical logarithmic scale interval,
including the final genuine blocking step at every finite cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportHarvestUpperAge
open Filter Lattice RG Wilson PhysicalNext.Repeat.Legato WilsonReportHarvestSourceReach
open scoped Topology
variable {G:Gauge} (R:Run G) (simple:G.Simple)
include simple

/-- The last block itself costs one power of its lower temperature, before picking a cutoff. -/
theorem block :
    ∀ᶠ j:ℕ in atTop, ((R.family.S.block j).val:ℝ) ≤ R.family.path.levels.clock.hatBeta j := by
  let A:=R.family.path.levels
  filter_upwards [A.fits.deep.eventually_ge_atTop 1,
    (Next.Rank.Station.hat_rate A simple).eventually_ge_atTop (G.slopeConstant+2)] with j hj hot
  let L:ℝ:=(A.S.block j).val
  have lp:0<L:=by dsimp only [L];exact_mod_cast (A.S.block j).pos
  have c:= (Gauge.slopeConstant_pos simple).le
  have q:=ActualRunRatioGrowth.ratio_power_le R simple j 1 hj
  change L^2 ≤ A.clock.hatBeta (j+1) at q
  have shift : A.clock.hatBeta (j+1)=A.clock.hatBeta j+G.slopeConstant*Real.log L := by
    unfold Calendar.hatBeta;rw [Schedule.scale_succ];ring
  rw [shift] at q
  have cost:G.slopeConstant*Real.log L ≤ G.slopeConstant*L :=
    mul_le_mul_of_nonneg_left ((Real.log_le_sub_one_of_pos lp).trans (by linarith)) c
  change L ≤ A.clock.hatBeta j
  by_contra! larger
  have bound:L*(G.slopeConstant+1)<L*L:=mul_lt_mul_of_pos_left (by linarith) lp
  nlinarith only [q,cost,larger,bound]

/-- Throughout the top half measured at the true penultimate scale, the entire
microscopic mesh ratio costs two current-scale powers and two temperature powers. -/
theorem interval :
    ∀ᶠ m:ℕ in atTop, ∀ n≥m, ∀ j≥m, j ≤ n →
      R.family.S.scale n-R.family.S.scale m ≤ 2*(R.family.S.scale j-R.family.S.scale m) →
      R.family.S.a m/R.family.S.a (n+1) ≤
        (R.family.S.a m/R.family.S.a j)^2*(R.family.path.levels.clock.hatBeta j)^2 := by
  let A:=R.family.path.levels
  let S:=R.family.S
  obtain ⟨base,steps⟩:=eventually_atTop.mp (block R simple)
  obtain ⟨hot,heat⟩:=eventually_atTop.mp ((Next.Rank.Station.hat_rate A simple).eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop base,eventually_ge_atTop hot] with m mb mh
  intro n mn j mj _ half
  let x:=A.clock.hatBeta j
  have hi:2 ≤ x:=heat j (mh.trans mj)
  have bm:0 < A.clock.hatBeta m:=zero_lt_one.trans (A.fits.delayed m)
  have sale:(S.block n).val ≤ (A.clock.hatBeta n:ℝ):=steps n (mb.trans mn)
  have slope:=mul_le_mul_of_nonneg_left half (Gauge.slopeConstant_pos simple).le
  have cov:A.clock.hatBeta n ≤ 2*x:=by
    dsimp only [x,Calendar.hatBeta] at bm ⊢
    linarith only [slope,bm]
  have bill:((S.block n).val:ℝ) ≤ x^2:=sale.trans (cov.trans (by nlinarith [mul_nonneg (show 0 ≤ x-2 by linarith) (show 0 ≤ x by linarith)]))
  have lower:0 ≤ (S.a m/S.a j)^2:=sq_nonneg _
  have rung:0<((S.block n).val:ℝ):=by exact_mod_cast (S.block n).pos
  have identity:S.a m/S.a (n+1)=Real.exp (elapsed S m n)*(S.block n).val:=by
    rw [←mesh,elapsed,Schedule.scale_succ,show S.scale n+Real.log (S.block n).val-S.scale m=(S.scale n-S.scale m)+Real.log (S.block n).val by ring,Real.exp_add,Real.exp_log rung]
    rfl
  have duration:Real.exp (elapsed S m n) ≤ (S.a m/S.a j)^2:=by
    rw [←mesh,←Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by simpa only [Nat.cast_ofNat,elapsed] using half)
  rw [identity]
  exact mul_le_mul duration bill rung.le lower

end YM.Integration.WilsonReportHarvestUpperAge
