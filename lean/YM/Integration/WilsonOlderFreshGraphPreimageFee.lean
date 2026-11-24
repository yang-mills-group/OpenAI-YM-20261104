import YM.Integration.WilsonOlderFreshGraphSlowPreimages
import YM.Integration.WilsonMeasuredLandedCurrency

/-! The physical engineering sum over the children is paid in the actual
coupling on the same marked course, uniformly before both regulators. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphPreimageFee
open Function Filter Finset Lattice Wilson RG FormalBulk08
open Dawn Annex Elm
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Boulevard
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)

def first (d:ℕ):ℕ:=(eventually_atTop.mp (WilsonOlderFreshGraphSlowPreimages.block R simple slow d
  (show 0 < (1:ℝ) by norm_num))).choose

include simple slow in
theorem original {j N per:ℕ} (jN:j+1≤N)(late:WilsonMeasuredLandedCurrency.first R simple≤j)
    (d p:ℕ)(paid:first R simple slow d≤j+1){ε:ℝ}(ep:0≤ε){D:ℕ}(f:Studio D)
    (fare:Site (R.family.path.levels.S.block (j+1)) → ℝ)
    (h:Site (R.family.path.levels.S.block (j+1)) → ℂ)
    (hw:∀z,‖h z‖≤((R.family.path.levels.S.block (j+1)).val:ℝ)^d/
      ((R.family.path.levels.S.block (j+1)).val:ℝ)^4)
    (hf:∀z,fare z≤(ε/8)*((Pert.Asymptotics.regulatorRun R.family N per j)^(p+2))*
      (1+‖Annex.compress D (Dawn.throughW z D (Elm.growL R.family.path.levels (j+1)) f)‖))
    (hn:∀z,0≤fare z):
    (∑z,‖h z‖*fare z) ≤ ε*(Pert.Asymptotics.regulatorRun R.family N per j)^p*(1+‖Annex.compress D f‖):=by
  let b:=((R.family.path.levels.S.block (j+1)).val:ℝ)
  let β:=R.alloy.B.a.clock.hatBeta ((j+1)+1)
  let g:=Pert.Asymptotics.regulatorRun R.family N per j
  let mass:=1+‖Annex.compress D f‖
  have band:=WilsonMeasuredLandedCurrency.native R simple per jN late
  have gp:0<g:=band.2.1
  have damp:β*g^2≤8:=band.2.2.1
  have geom : b^d ≤ β := by
    have levels : R.family.path.levels=R.alloy.B.a := rfl
    dsimp only [b,β]
    rw [levels]
    simpa only [Real.rpow_one] using (eventually_atTop.mp
      (WilsonOlderFreshGraphSlowPreimages.block R simple slow d (show 0<(1:ℝ) by norm_num))).choose_spec (j+1) paid
  have masspos:0 ≤ mass:=by dsimp [mass];positivity
  have engineering:=WilsonOlderFreshGraphChildFare.engineering (R.family.path.levels.S.block_odd (j+1))
    (Elm.growL R.family.path.levels (j+1)) f d ((ε/8)*g^(p+2)) (by positivity) fare hf
  calc
    _ ≤ ∑z,(b^d/b^4)*fare z:=Finset.sum_le_sum fun z _=>mul_le_mul_of_nonneg_right (hw z) (hn z)
    _ ≤ b^d*((ε/8)*g^(p+2))*mass:=engineering
    _ ≤ β*((ε/8)*g^(p+2))*mass:=by gcongr
    _ = (β*g^2)*((ε/8)*g^p*mass):=by rw [pow_add];ring
    _ ≤ 8*((ε/8)*g^p*mass):=mul_le_mul_of_nonneg_right damp (by positivity)
    _ = _:=by ring
end YM.Integration.WilsonOlderFreshGraphPreimageFee
end
