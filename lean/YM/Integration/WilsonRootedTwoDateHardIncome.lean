import YM.Integration.WilsonRootedTwoDateHardMode
import YM.Integration.QLocalThermalJoinedForcedRegister

/-! One occupied marker cancels one common radius in the original hard tariff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateHardIncome
open Function Finset Lattice RG Wilson Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison Comparison.Density.RenderM LocalComparison.Global RG.Supply
open Push.AbsoluteSums QLocalThermalJoinedRate QLocalThermalJoinedForcedRegister
open WilsonRootedTwoDateHardMode ActualWilsonDirtyPartners
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {D : V → ComparisonDensity.Address.Orbit} (M : MarkedPackets D G n Γ)
    {P : Rep G n} {o : V → Site n} (p : BudgetPoint) (T : Taste X o P Γ)

omit [Fintype V] in
private theorem charge_scaled (off : ℕ) (s τ amount : ℝ) :
    charge M p off (s*(τ*amount)) = (s*τ)*charge M p off amount := by
  unfold charge
  ring

theorem refund (off : ℕ) {s τ κ : ℝ} (hs : 0<s) (ht : 0<τ) (hk : 0<κ) (b k amount : ℝ)
    (w : V → ℝ) (z : Γ.Mode) (j : ℕ) (card : z.val.card=j+1) :
    (Poly.toll w z * ((s*τ)^z.val.card)⁻¹) * (κ*(s*b+increase M p off (s*(τ*amount)) κ k (s*b))) =
    (Poly.toll w z * ((s*τ)^j)⁻¹) * (κ*b/τ + 2*(Fintype.card Γ.Mode:ℝ)*(k+(Fintype.card V:ℝ)*(κ*(s*b)))*charge M p off amount) := by
  rw [card,pow_succ,increase,charge_scaled]
  field_simp [hs.ne',ht.ne',hk.ne',pow_ne_zero j (mul_ne_zero hs.ne' ht.ne')]

/-- The original external allowance with one factor restored for each further mark. -/
def Earned (off : ℕ) (s τ κ b k amount : ℝ) : Prop :=
  ∀ w : V → ℝ,(∀ v,0<w v) → ∀ (z : Γ.Mode) (v : V),v∈z.val → ∀ j : ℕ,z.val.card=j+1 → ∀ (x : X) (U : Config G n),
    SumBudget (row p T w z x U) ((Poly.toll w z * ((s*τ)^j)⁻¹) *
      (κ*b/τ+2*(Fintype.card Γ.Mode:ℝ)*(k+(Fintype.card V:ℝ)*(κ*b))*charge M p off amount))

theorem earn (off : ℕ) {s τ κ b k amount : ℝ} (hs : 0<s) (ht : 0<τ) (hk : 0<κ) (small : s≤1) (hb : 0≤b) (cost : 0≤amount)
    (paid : Released p T (s*τ) κ (s*b+increase M p off (s*(τ*amount)) κ k (s*b))) : Earned M p T off s τ κ b k amount := by
  intro w hw z v seen j card x U
  apply budget_loosen (paid w hw z v seen x U)
  rw [refund M p off hs ht hk _ _ _ _ _ _ card]
  have charge0 : 0≤charge M p off amount := by
    have := p.exponent_pos
    unfold charge blockSites
    positivity
  have old : s*b≤b := mul_le_of_le_one_left hb small
  have factor0 : 0≤Poly.toll w z * ((s*τ)^j)⁻¹ := mul_nonneg (Poly.worth hw z).le (inv_nonneg.mpr (pow_nonneg (mul_pos hs ht).le _))
  apply mul_le_mul_of_nonneg_left _ factor0
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ charge0
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left old hk.le) (Nat.cast_nonneg _)

end YM.Integration.WilsonRootedTwoDateHardIncome
