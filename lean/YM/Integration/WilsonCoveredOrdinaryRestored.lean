import YM.Integration.WilsonReceivedCloseOrdinaryGrade
import YM.Integration.WilsonCoveredOrdinaryWindingPost

/-! Restoring a finite original source after the finite-to-cover change reuses its actual
per-face price and the true close-interval coupling band. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoveredOrdinaryRestored
open Finset Marker Multi
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] {J:Census V}

theorem paid (s:J.Mode) (a d q:ℕ) (U g t tol w value:ℝ) (unit:1≤U)
    (gp:0<g) (cool:g≤1) (tp:0<t) (edge:t≤3*g) (inverse:t⁻¹≤3*g⁻¹)
    (wp:0<w) (vp:0≤value) (active:s.val.card≤a) (cash:w⁻¹≤(U*(g⁻¹)^d)^s.val.card)
    (onset:WilsonReceivedCloseOrdinaryGrade.invoice J a d q U*g≤tol)
    (weighted:
      let power:=q+d*a+1+a
      let E:=(3:ℝ)⁻¹^power*t^power
      w*value≤∑h∈shards J s,(h.val.card:ℝ)*E*(t⁻¹+E)^h.val.card) :
    value≤tol*g^q := by
  let power:=q+d*a+1+a
  let E:=(3:ℝ)⁻¹^power*t^power
  change w*value≤∑h∈shards J s,(h.val.card:ℝ)*E*(t⁻¹+E)^h.val.card at weighted
  have ep:0≤E := by dsimp [E];positivity
  have exchange:E≤g^power := by
    have tar : (3:ℝ)⁻¹*t ≤ g := by linarith only [edge]
    change (3:ℝ)⁻¹^power*t^power ≤ _
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) tar _
  let price:=(U*(g⁻¹)^d)^s.val.card
  have pp:0≤price := by dsimp [price];positivity
  have sell:=WilsonReceivedCloseOrdinaryGrade.earned J s a d q unit gp cool tp edge inverse active (value:=value)
  have bill:value≤WilsonReceivedCloseOrdinaryGrade.invoice J a d q U*g^(q+1) := by
    apply sell
    calc
      _ = w⁻¹*(w*value) := by field_simp
      _ ≤ price*(∑ h∈shards J s,(h.val.card:ℝ)*E*(t⁻¹+E)^h.val.card) :=
        mul_le_mul cash weighted (mul_nonneg wp.le vp) pp
      _ ≤ price*(∑ h∈shards J s,(h.val.card:ℝ)*g^power*(t⁻¹+g^power)^h.val.card) := by
        apply mul_le_mul_of_nonneg_left _ pp
        exact sum_le_sum (fun h _=>mul_le_mul (mul_le_mul_of_nonneg_left exchange (Nat.cast_nonneg _))
          (pow_le_pow_left₀ (add_nonneg (inv_nonneg.mpr tp.le) ep) (add_le_add le_rfl exchange) _)
          (pow_nonneg (add_nonneg (inv_nonneg.mpr tp.le) ep) _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg gp.le _)))
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (mul_nonneg (pow_nonneg tp.le _) (Nat.cast_nonneg _))) pp
  calc
    value ≤ _ := bill
    _ = (WilsonReceivedCloseOrdinaryGrade.invoice J a d q U*g)*g^q := by rw [pow_succ];ring
    _ ≤ tol*g^q := mul_le_mul_of_nonneg_right onset (pow_nonneg gp.le _)

end YM.Integration.WilsonCoveredOrdinaryRestored
