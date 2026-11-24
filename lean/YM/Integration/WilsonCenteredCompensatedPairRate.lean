import YM.Comparison.RG02.Cumulants.Parents
import YM.Marker.Weight

/-! The low signed coefficient of the complete density for two child marks and
their filed counterterm, including the two changes in the product of singleton
means. The charged income is the original connected-field tariff. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCompensatedPairRate
open Marker Extra.Trajectories Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

theorem exact_pair (a b c : V) (s : R.Mode) (apart : a ≠ b) (pair : s.val = {a,b})
    (Y T : Poly R) (quiet : Y.part R.quiet = 1) (filed : T.part R.quiet = 0) :
    let Q := Poly.pass T
    let D := connected Y - T
    (Y.part s - Y.part (R.fire c)) - (Q.part s - Q.part (R.fire c)) =
      D.part s - D.part (R.fire c) + D.part (R.fire a) * Y.part (R.fire b)
        + Q.part (R.fire a) * D.part (R.fire b) := by
  intro Q D
  have normQ : Q.part R.quiet = 1 := Poly.pass_part _ filed
  have E : connected Q = T := connected_pass filed
  have dm (m : R.Mode) : D.part m = (connected Y).part m - (connected Q).part m := by
    rw [E]
    rfl
  rw [dm s, dm (R.fire c), dm (R.fire a), dm (R.fire b),
    twins a b s Y quiet apart pair, twins a b s Q normQ apart pair,
    lamp c Y quiet, lamp c Q normQ, lamp a Y quiet, lamp a Q normQ,
    lamp b Y quiet, lamp b Q normQ]
  ring

theorem paid (a b c : V) (s : R.Mode) (apart : a ≠ b) (pair : s.val = {a,b})
    (Y T : Poly R) (quiet : Y.part R.quiet = 1) (filed : T.part R.quiet = 0)
    (w : V → ℝ) (fee : ℝ)
    (income : ∀ u : R.Mode, ∀ i ∈ u.val,
      ‖(connected Y - T).part u‖ ≤ (Poly.toll w u)⁻¹ * fee) :
    let Q := Poly.pass T
    ‖(Y.part s - Y.part (R.fire c)) - (Q.part s - Q.part (R.fire c))‖ ≤
      (Poly.toll w s)⁻¹ * fee + (w c)⁻¹ * fee
        + ((w a)⁻¹ * fee) * ‖Y.part (R.fire b)‖
        + ‖Q.part (R.fire a)‖ * ((w b)⁻¹ * fee) := by
  intro Q
  let D := connected Y - T
  have pairFee : ‖D.part s‖ ≤ (Poly.toll w s)⁻¹ * fee :=
    income s a (by simp [pair])
  have single (v : V) : ‖D.part (R.fire v)‖ ≤ (w v)⁻¹ * fee := by
    simpa only [Poly.toll,Census.fire,Finset.prod_singleton] using
      income (R.fire v) v (Finset.mem_singleton_self v)
  rw [exact_pair a b c s apart pair Y T quiet filed]
  calc
    _ ≤ (‖D.part s - D.part (R.fire c)‖
          + ‖D.part (R.fire a) * Y.part (R.fire b)‖)
          + ‖Q.part (R.fire a) * D.part (R.fire b)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [norm_mul,norm_mul]
      exact add_le_add
        (add_le_add ((norm_sub_le _ _).trans (add_le_add pairFee (single c)))
          (mul_le_mul_of_nonneg_right (single a) (norm_nonneg _)))
        (mul_le_mul_of_nonneg_left (single b) (norm_nonneg _))

end YM.Integration.WilsonCenteredCompensatedPairRate
