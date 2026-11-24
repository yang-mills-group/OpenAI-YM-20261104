import YM.Integration.WilsonRootedTwoDateHardIncome
import YM.Integration.WilsonRootedTwoDateHardClockCost

/-! Fixed external costs for every occupied mode of the shared original hard catalogue. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardEconomy
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM LocalComparison.Global RG.Supply
open Push.AbsoluteSums QLocalThermalJoinedRate QLocalThermalJoinedForcedRegister
open WilsonRootedTwoDateHardMode ActualWilsonDirtyPartners
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {D : V → ComparisonDensity.Address.Orbit} (M : MarkedPackets D G n Γ)
    {P : Rep G n} {o : V → Site n} (p : BudgetPoint) (T : Taste X o P Γ)

def External (off : ℕ) (τ h κ b k amount : ℝ) : Prop :=
  ∀ w : V → ℝ,(∀ v,0<w v) → ∀ (z : Γ.Mode) (v : V),v∈z.val → ∀ j : ℕ,z.val.card=j+1 → ∀ (x : X) (U : Config G n),
    SumBudget (row p T w z x U) ((Poly.toll w z * (τ^j)⁻¹ * h) *
      (κ*b/τ+2*(Fintype.card Γ.Mode:ℝ)*(k+(Fintype.card V:ℝ)*(κ*b))*charge M p off amount))

theorem spent (off : ℕ) {s τ h κ b k amount : ℝ} (hs : 0<s) (ht : 0<τ)
    (cap : ∀j : ℕ,j≤Fintype.card V → (s^j)⁻¹≤h) (bill : WilsonRootedTwoDateHardIncome.Earned M p T off s τ κ b k amount) :
    External M p T off τ h κ b k amount := by
  intro w hw z v seen j card x U
  have issued := bill w hw z v seen j card x U
  have size := Finset.card_le_univ z.val
  have jsize : j≤Fintype.card V := by omega
  have price0 := (budget_nonneg issued)
  have base : 0<Poly.toll w z*((s*τ)^j)⁻¹ := mul_pos (Poly.worth hw z) (inv_pos.mpr (pow_pos (mul_pos hs ht) _))
  have positive := nonneg_of_mul_nonneg_right price0 base
  apply budget_loosen issued
  apply mul_le_mul_of_nonneg_right _ positive
  rw [mul_pow,mul_inv_rev,←mul_assoc]
  exact mul_le_mul_of_nonneg_left (cap j jsize) (mul_nonneg (Poly.worth hw z).le (inv_nonneg.mpr (pow_nonneg ht.le _)))

end YM.Integration.WilsonRootedTwoDateHardEconomy
