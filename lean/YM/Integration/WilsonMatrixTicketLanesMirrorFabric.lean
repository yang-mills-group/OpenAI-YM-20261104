import YM.Integration.WilsonMatrixTicketLanesMirrorClock
import YM.Integration.WilsonCoefficientPreparation
import YM.FVA2.CommonCalendar

/-! The full-period and inversion-period Gaussian prescription on the original finite trajectory. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesMirrorFabric
open Filter RG Lattice FVA2 FVA2.CityHistory FVA2.Both.Passage FVA2.Both.Passage.Cohort
open PhysicalNext.Repeat.Legato WilsonMatrixTicketLanesMirrorClock
open scoped Topology Classical
variable {G : Gauge}

/-- Every step of the authentic late physical segment meets the size and branch conditions
required by the paired Schur covariance construction, before any period or upper cutoff. -/
theorem long (H : History G) : ∀ᶠ b : ℕ in atTop, ∀ (p k : ℕ) (σ : Picks H p),
    Long (segment H p b σ k) := by
  filter_upwards [purchased H] with b hb p k σ
  induction k with
  | zero => trivial
  | succ k ih => exact ⟨hb p (k+1) k (Nat.lt_succ_self k),ih⟩

/-- The very same registered chart and occupied running beta costs support the paired
Gaussian recursion and the inversion prescription for every submitted formal source. -/
theorem original (R : Run G) : ∀ᶠ b : ℕ in atTop,
    ∀ (p k : ℕ) (σ : Picks R.family.path p),
      let H := R.family.path
      let L := segment H p b σ k
      ∃ (B : Long L) (E : Exhibit L), E.chart = R.metals.O ∧
        E.quotes = quotes H p b k ∧
        (∀ j, rates E.quotes k j = Delay.stones (offset H p b k) j) ∧
        ∀ Q : Warehouse G, CapReady.Article Q L E B := by
  filter_upwards [long R.family.path] with b hb p k σ
  let H := R.family.path
  let L := segment H p b σ k
  let B : Long L := hb p k σ
  let E : Exhibit L := ⟨R.metals.O,R.alloy.B.ratio,quotes H p b k,sound H p b k,first H p b k⟩
  exact ⟨B,E,rfl,rfl,read_back H p b k,fun Q => CapReady.issuance E B Q⟩

end YM.Integration.WilsonMatrixTicketLanesMirrorFabric
