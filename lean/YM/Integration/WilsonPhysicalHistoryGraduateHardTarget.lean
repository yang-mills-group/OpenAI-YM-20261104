import YM.Integration.WilsonPhysicalHistoryFiniteTicketTarget
import YM.QuadraticLocal.Manifold

/-! Convert the hard allowance in the authentic MixedResets day payment at
the external weights of the filed graduate into all physical coupling orders. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryGraduateHardTarget
open Filter Real Lattice Wilson RG Source Marker QuadraticLocal Pert.Asymptotics
open scoped Topology Classical

variable {G : Gauge} (C : Family G) (M : C.Makes) (simple : G.Simple)
  (order : ℕ) (ε : ℝ) (positive : 0 < ε)

include M simple positive in
private theorem calendar :
    ∀ᶠ k : ℕ in atTop, ∀ i, k ≤ i → ∀ N n, i ≤ N →
      sqrt (C.path.levels.clock.forcedAllowance i) ≤ ε*(regulatorRun C N n i)^order := by
  filter_upwards [WilsonPhysicalHistoryFiniteTicketTarget.physical C M simple 1 order 0
      (b:=1) zero_le_one positive] with k fee
  intro i late N n cut
  have full := fee i late N n cut 1 (by simp)
  have sum : sqrt (C.path.levels.clock.forcedAllowance i) ≤
      C.path.levels.clock.forcedAllowance i + sqrt (C.path.levels.clock.forcedAllowance i) :=
    le_add_of_nonneg_left (exp_pos _).le
  exact sum.trans (by simpa using full)

include M simple positive in
def onset : ℕ := (eventually_atTop.1 (calendar C M simple order ε positive)).choose

include M simple positive in
theorem paid {V T : Type*} [DecidableEq V] {Z : Census V} {i b sx N n : ℕ}
    (late : onset C M simple order ε positive ≤ i) (cut : i ≤ N)
    (P : Rep G (C.side i n)) (o : V → Site (C.side i n))
    (H : Hard T P.p P.activities.forced P.activities.K o Z) (w : V → ℝ)
    {old : ℝ} (budget : H.Paid w P.p.B P.p.supportExponent
      (min ((C.path.levels.clock.hatBeta b)^(-(sx:ℝ)) * sqrt (C.path.levels.clock.forcedAllowance i)) old)) :
    H.Paid w P.p.B P.p.supportExponent (ε*(regulatorRun C N n i)^order) := by
  have bound := (eventually_atTop.1 (calendar C M simple order ε positive)).choose_spec i late i le_rfl N n cut
  have raised : (C.path.levels.clock.hatBeta b)^(-(sx:ℝ)) ≤ 1 :=
    rpow_le_one_of_one_le_of_nonpos (C.path.levels.fits.delayed b).le
      (neg_nonpos.mpr (Nat.cast_nonneg sx))
  refine H.mono budget ((min_le_left ..).trans ((mul_le_mul_of_nonneg_right raised (sqrt_nonneg _)).trans ?_))
  simpa only [one_mul] using bound

end YM.Integration.WilsonPhysicalHistoryGraduateHardTarget
end

