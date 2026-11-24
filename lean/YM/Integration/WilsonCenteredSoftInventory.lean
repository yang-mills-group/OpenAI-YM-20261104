import YM.Integration.WilsonCenteredOwnerIntake

/-! Value-level data of regular marked words for the original forced collector.
All price and measurability statements refer to the actual signed summands. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredSoftInventory
open Wilson RG Lattice Push.Local Planned.GuardedAtom
variable {G : Gauge} {n : Side}

structure Receipt (P : Rep G n) (Z : Support n) (Q : Config G n→ℂ) (bill : ℝ) where
  Row : Type
  counted : Countable Row
  ground : Row→Support n
  value : Row → Config G n→ℂ
  price : Row→ℝ
  holds : ∀i,Z⊆ground i
  gauge : ∀i,GaugeInvariant (value i)
  borel : ∀i,Measurable (value i)
  uses : ∀i,UsesFinal P.p.threshold (ground i) (value i)
  nonnegative : ∀i,0≤price i
  cap : ∀i U,‖value i U‖≤price i
  cash : SumBudget (fun i=>reservedMass P.p (ground i) (price i)) bill
  posted : ∀ U, HasSum (fun i=>value i U) (Q U)

end YM.Integration.WilsonCenteredSoftInventory
