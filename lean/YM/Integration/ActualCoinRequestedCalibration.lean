import YM.Integration.NativeKineticCalibration
import YM.Integration.ActualRunAdmissionScales
import YM.IterationFour.Vacuum.Step

/-! The actual native Coin is tested in any fixed requested norm. Only norm
orders and support exponent change; threshold and all physical functions remain
literal. Native Decent transfers because it uses only B and threshold. The full
reset activities, render list and gas remain at the original native budget.
The requested Width receipt and the selected-Coin construction remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualCoinRequestedCalibration
open WilsonStartup Lattice Wilson RG IterationFour IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection FullQLocal
open Currency Render ActualRunAdmissionScales
open scoped BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {N q i : ℕ}
variable {S : List (Piece G (C.side i q))} {U : Rep G (C.side i q)}
variable {x γ l : ℝ}
variable (ord pow : ℕ) (supp : ℝ) (hord : 6 ≤ ord) (hpow : 2 ≤ pow)
  (hsupp : 0 < supp)
local notation "p!" => requestedBudget C.path.levels i ord pow supp hord hpow hsupp

private theorem original_paths (ht : C.Makes) (hi : i ≤ N) :
    (C.path.rep N q i).path.Bounds (C.path.levels.params i).clip
      (C.path.levels.params i).width (C.path.levels.params i).paths
      (C.path.levels.clock.loopCap i) := by
  have hs : C.path.Conv N q i := ht.wilson.represents N q i hi
  rw [← hs.clip]
  exact hs.good.paths

/-- The quoted scalar is the actual post-reset beta discrepancy. -/
def calibration (ht : C.Makes) (hi : i ≤ N)
    (h : Coin C N q i S U x γ l)
    (hd : Decent (C.path.levels.params i).clip (C.path.levels.budget i))
    (hw : Geo.Width p! (C.path.levels.params i).clip
      (C.path.levels.params i).width) :
    CalibrationPresentation (loaded C N q i S U) p!
      (NativeKineticCalibration.price G (C.path.levels.params i).clip
        p! (C.path.levels.params i).width
        (C.path.levels.params i).paths (U.beta - C.path.β N q i)) :=
  NativeKineticCalibration.calibration (p := p!) (original_paths (q := q) ht hi)
    ⟨hd.direct, hd.radius, hd.cut⟩ hw
    (loaded C N q i S U)
    (show (C.path.levels.budget i).threshold = U.p.threshold from
      congrArg BudgetPoint.threshold h.types.budget.symm) (U.beta - C.path.β N q i)

/-- The full clipped kinetic action is retained, including every native row. -/
theorem amount (ht : C.Makes) (hi : i ≤ N)
    (h : Coin C N q i S U x γ l)
    (hd : Decent (C.path.levels.params i).clip (C.path.levels.budget i))
    (hw : Geo.Width p! (C.path.levels.params i).clip
      (C.path.levels.params i).width) (V : Config G (C.side i q)) :
    (calibration ord pow supp hord hpow hsupp ht hi h hd hw).amount V =
      (U.beta - C.path.β N q i) *
        Push.BetaTransport.kinetic (C.path.rep N q i).path
          (C.path.levels.params i).clip (C.path.levels.budget i) V := by
  exact NativeKineticCalibration.amount (p := p!) (original_paths (q := q) ht hi)
    ⟨hd.direct, hd.radius, hd.cut⟩ hw
    (loaded C N q i S U)
    (show (C.path.levels.budget i).threshold = U.p.threshold from
      congrArg BudgetPoint.threshold h.types.budget.symm) (U.beta - C.path.β N q i) V

/-- No additional scalar estimate is assumed: this uses Coin.extraBeta. -/
theorem price_le (ht : C.Makes) (hi : i ≤ N)
    (h : Coin C N q i S U x γ l)
    (hw : Geo.Width p! (C.path.levels.params i).clip
      (C.path.levels.params i).width) :
    NativeKineticCalibration.price G (C.path.levels.params i).clip
        p! (C.path.levels.params i).width
        (C.path.levels.params i).paths (U.beta - C.path.β N q i) ≤
      l * NativeKineticCalibration.unitCost G (C.path.levels.params i).clip
        p! (C.path.levels.params i).width
        (C.path.levels.params i).paths :=
  NativeKineticCalibration.price_le (original_paths (q := q) ht hi) hw h.extraBeta

/-- Exact base-plus-layers action, original reset remainder and nonzero calibration. -/
theorem exponent (ht : C.Makes) (hi : i ≤ N)
    (h : Coin C N q i S U x γ l)
    (hd : Decent (C.path.levels.params i).clip (C.path.levels.budget i))
    (hw : Geo.Width p! (C.path.levels.params i).clip
      (C.path.levels.params i).width) (V : Config G (C.side i q)) :
    (loaded C N q i S U).exponent V =
      (C.path.rep N q i).scalar -
        (C.path.rep N q i).path.inChannels (C.path.levels.params i).clip
          (C.path.levels.budget i) (C.path.β N q i) V -
        renders (prefactor (g C N q i)) (C.path.levels.budget i) V S -
        U.activities.additive (C.path.levels.budget i) V -
        (calibration ord pow supp hord hpow hsupp ht hi h hd hw).amount V := by
  have hp : permits S U.p := by
    rw [h.types.budget]
    exact h.lives
  have he : U.activities.Valid U.p x γ := by
    rw [h.types.budget]
    exact h.error
  have ha := Render.additive (prefactor (g C N q i)) hp he V
  change (loaded C N q i S U).activities.additive U.p V = _ at ha
  rw [h.read_exponent ht hi V, ha, amount ord pow supp hord hpow hsupp ht hi h hd hw V]
  rw [h.types.stencil, h.types.clip, h.types.budget]
  ring

/-- The same original trajectory density, with its full original reset gas. -/
theorem actual_density (ht : C.Makes) (hi : i ≤ N)
    (h : Coin C N q i S U x γ l)
    (hd : Decent (C.path.levels.params i).clip (C.path.levels.budget i))
    (hw : Geo.Width p! (C.path.levels.params i).clip
      (C.path.levels.params i).width) (V : Config G (C.side i q)) :
    (C.path.rep N q i).eval V =
      Real.exp ((C.path.rep N q i).scalar -
        (C.path.rep N q i).path.inChannels (C.path.levels.params i).clip
          (C.path.levels.budget i) (C.path.β N q i) V -
        renders (prefactor (g C N q i)) (C.path.levels.budget i) V S) *
      (Real.exp (-U.activities.additive (C.path.levels.budget i) V -
        (calibration ord pow supp hord hpow hsupp ht hi h hd hw).amount V) *
        U.activities.gas (C.path.levels.budget i) V) := by
  rw [← h.value]
  change Real.exp ((loaded C N q i S U).exponent V) *
    (loaded C N q i S U).activities.gas U.p V = _
  rw [exponent ord pow supp hord hpow hsupp ht hi h hd hw V]
  have hg := congrFun (Render.gas (prefactor (g C N q i)) U.activities S U.p) V
  change (loaded C N q i S U).activities.gas U.p V = _ at hg
  rw [hg, h.types.budget]
  rw [show (C.path.rep N q i).scalar -
      (C.path.rep N q i).path.inChannels (C.path.levels.params i).clip
        (C.path.levels.budget i) (C.path.β N q i) V -
      renders (prefactor (g C N q i)) (C.path.levels.budget i) V S -
      U.activities.additive (C.path.levels.budget i) V -
      (calibration ord pow supp hord hpow hsupp ht hi h hd hw).amount V =
    ((C.path.rep N q i).scalar -
      (C.path.rep N q i).path.inChannels (C.path.levels.params i).clip
        (C.path.levels.budget i) (C.path.β N q i) V -
      renders (prefactor (g C N q i)) (C.path.levels.budget i) V S) +
    (-U.activities.additive (C.path.levels.budget i) V -
      (calibration ord pow supp hord hpow hsupp ht hi h hd hw).amount V) by ring,
    Real.exp_add, mul_assoc]

end YM.Integration.ActualCoinRequestedCalibration
end
