import YM.Integration.ActualRunRequestedNorm
import YM.Integration.ActualRunFixedOrders
import YM.Integration.ActualRepeatedNorm
import YM.Integration.ActualRunStageReceipts

/-! Actual requested-norm admission on the original Run. The already-returned
profile and StageReceipts supply every numerical comparison. One tail is
chosen before cutoff and period; the full representation and its regular
allowance are unchanged. No support-growth or smallness premise is added. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunRequestedNormTail
open Filter RG PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge}

/-- The literal fine representation is well formed at the same fixed norm
used along the trajectory. Its cost is the original clock allowance, not a
newly chosen bound. Both retained receipts belong to this same Run. -/
theorem eventually_wellFormed (R : Run G) (hReceipts : StageReceipts R)
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧
      j ≤ (R.metals.p.profile j).power)
    (fieldOrder distanceOrder : ℕ) (support : ℝ)
    (hfield : 6 ≤ fieldOrder) (hdistance : 2 ≤ distanceOrder)
    (hsupport : 0 < support) (hcap : support ≤ 100) :
    ∀ᶠ m : ℕ in atTop, ∀ N period : ℕ, m < N →
      ∃ W : LocalComparison.Global.WellFormed
        (ActualRepeatedNorm.atLevel R.family fieldOrder distanceOrder support
          hfield hdistance hsupport (m + 1))
        (R.family.path.rep N period (m + 1)),
        W.regularCost = R.family.path.levels.clock.allowance (m + 1) := by
  filter_upwards [ActualRunFixedOrders.eventually_orders R hprofile
    fieldOrder distanceOrder] with m hm N period hN
  have hlevel : m + 1 ≤ N := Nat.succ_le_of_lt hN
  have hvac : (R.family.path.rep N period (m + 1)).p =
      R.family.path.levels.budget (m + 1) :=
    (R.makes.wilson.represents N period (m + 1) hlevel).vac
  let Q := ActualRepeatedNorm.atLevel R.family fieldOrder distanceOrder support
    hfield hdistance hsupport (m + 1)
  have ht : Q.threshold =
      (R.family.path.rep N period (m + 1)).p.threshold := by
    change (R.family.path.levels.budget (m + 1)).threshold = _
    rw [hvac]
  have hB : Q.B = (R.family.path.rep N period (m + 1)).p.B := by
    change (R.family.path.levels.budget (m + 1)).B = _
    rw [hvac]
  have ho : Q.order ≤ (R.family.path.rep N period (m + 1)).p.order := by
    change fieldOrder ≤ _
    rw [hvac]
    exact hm.1
  have hp : Q.power ≤ (R.family.path.rep N period (m + 1)).p.power := by
    change distanceOrder ≤ _
    rw [hvac]
    exact hm.2
  have hs : Q.supportExponent ≤
      (R.family.path.rep N period (m + 1)).p.supportExponent := by
    change support ≤ _
    rw [hvac]
    apply hcap.trans
    change 100 ≤ (R.alloy.B.a.budget (m + 1)).supportExponent
    exact hReceipts.support (m + 1)
  exact ⟨ActualRunRequestedNorm.wellFormed R N period (m + 1) hlevel
    Q ht hB ho hp hs, rfl⟩

end YM.Integration.ActualRunRequestedNormTail
end
