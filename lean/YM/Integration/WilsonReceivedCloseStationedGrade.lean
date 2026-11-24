import YM.Integration.WilsonReceivedCloseFaceIncome

/-! Removing the actual birth radii once in the reported connected coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseStationedGrade
open Finset Lattice Marker
open scoped BigOperators Classical

def fee (u ε:ℝ) (a p:ℕ) := (1+2*ε*(3:ℝ)^p)*u^a

theorem nonneg {u ε:ℝ} (hu:1≤u) (he:0≤ε) (a p:ℕ) : 0 ≤ fee u ε a p := by
  unfold fee
  positivity

theorem grade {g u ε τ:ℝ} {a p d:ℕ} (gp:0<g) (cold:g≤1) (unit:1≤u)
    (ep:0≤ε) (birth:τ≤g^p) (reserve:d*a≤p) :
    (u*(g⁻¹)^d)^a*(g^(-(1:ℝ))*(τ+2*ε*(3*g)^p)) ≤
      fee u ε a p*(g^(-(1:ℝ))*g^(-(1:ℝ)))*g^(p-d*a) := by
  rw [Real.rpow_neg_one]
  let n:=d*a
  have gn:g^p=g^n*g^(p-n) := by rw [←pow_add,Nat.add_sub_of_le reserve]
  have u0:=zero_le_one.trans unit
  have fac:(u*(g⁻¹)^d)^a*(g⁻¹*((1+2*ε*(3:ℝ)^p)*g^p)) =
      fee u ε a p*g⁻¹*g^(p-n) := by
    rw [mul_pow,←pow_mul,gn]
    change u^a*(g⁻¹)^n*(g⁻¹*((1+2*ε*(3:ℝ)^p)*(g^n*g^(p-n))))=_
    rw [inv_pow]
    unfold fee
    field_simp
  have one:1≤g⁻¹:=(one_le_inv₀ gp).2 cold
  calc
    _ ≤ (u*(g⁻¹)^d)^a*(g⁻¹*((1+2*ε*(3:ℝ)^p)*g^p)) := by
      gcongr
      rw [mul_pow]
      linarith only [birth]
    _ = _ := fac
    _ ≤ fee u ε a p*(g⁻¹*g⁻¹)*g^(p-n) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right (inv_nonneg.mpr gp.le) one) (nonneg unit ep a p))
        (pow_nonneg gp.le _)

theorem remove {I:Type} [DecidableEq I] [Fintype I] {J:Census I} {s:J.Mode}
    {g u:ℝ} (gp:0<g) (cold:g≤1) (unit:1≤u) {d a:ℕ} (count:s.val.card≤a)
    (w:I→ℝ) (pos:∀i,0<w i) (born:∀i∈s.val,(w i)⁻¹≤u*(g⁻¹)^d) :
    Poly.toll (fun _=>1) s ≤ (u*(g⁻¹)^d)^a*Poly.toll w s := by
  have rate:1≤u*(g⁻¹)^d:=one_le_mul_of_one_le_of_one_le unit (one_le_pow₀ ((one_le_inv₀ gp).2 cold))
  have sale := WilsonReceivedCloseFaceBudget.product pos s (Finset.Subset.refl s.val) born
  have final := sale.trans (pow_le_pow_right₀ rate count)
  simp only [Poly.toll,Finset.prod_const_one]
  apply (div_le_iff₀ (Poly.worth pos s)).mp
  simpa only [one_div] using final

end YM.Integration.WilsonReceivedCloseStationedGrade
