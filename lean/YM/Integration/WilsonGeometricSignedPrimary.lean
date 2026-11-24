import YM.Integration.WilsonGeometricSignedPower

/-! The subtracted physical pair and its full horizon-zero coordinate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonGeometricSignedPrimary
open Finset Lattice RG Wilson Marker Multi QuadraticLocal Ac Source Labels Extra.Histories
open Push.Local Planned.GuardedAtom WilsonGeometricSignedCapture
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def pair (ab counter : (J).Mode) (a : ℂ) (s : (J).Mode) : ℂ :=
  (if s = ab then 1 else 0) - (if s = counter then a else 0)

theorem pair_value (ab counter : (J).Mode) (a : ℂ) (M : Poly J) :
    take (pair ab counter a) M = M.part ab - a * M.part counter := by
  simp [take,pair,sub_mul,sum_sub_distrib,ite_mul]

theorem pair_bill (ab counter : (J).Mode) (a : ℂ) (w : Fin 3 → ℝ) (positive : ∀ j, 0 < w j) :
    weightBill (pair ab counter a) w ≤ 1/Poly.toll w ab + ‖a‖/Poly.toll w counter := by
  have left (s : (J).Mode) : ‖if s=ab then (1:ℂ) else 0‖/Poly.toll w s =
      if s=ab then 1/Poly.toll w ab else 0 := by by_cases h : s = ab <;> simp [h]
  have right (s : (J).Mode) : ‖if s=counter then a else 0‖/Poly.toll w s =
      if s=counter then ‖a‖/Poly.toll w counter else 0 := by by_cases h : s = counter <;> simp [h]
  calc
    _ ≤ ∑ s:(J).Mode, (‖if s=ab then (1:ℂ) else 0‖ + ‖if s=counter then a else 0‖)/Poly.toll w s :=
      sum_le_sum fun s _ => div_le_div_of_nonneg_right (norm_sub_le ..) (Poly.worth positive s).le
    _ = (∑ s:(J).Mode, if s=ab then 1/Poly.toll w ab else 0) +
        (∑ s:(J).Mode, if s=counter then ‖a‖/Poly.toll w counter else 0) := by
      rw [←sum_add_distrib]
      exact sum_congr rfl fun s _ => by rw [add_div,left,right]
    _ = _ := by simp

theorem unit {G : Gauge} {n : Side} {F : Frame G 0} (h : Coefficient F n) (a : ℂ) {M : ℝ}
    (measured : ∀ q : Probe G 0, q.2.val=0 → runProbe F q h.x = a) (small : ‖a‖≤M) :
    F.coeffSize h.x ≤ testPrice F * M := by
  apply (probe_budget F).choose_spec.choose_spec.2 _ _ ((norm_nonneg a).trans small)
  intro q _
  exact (measured q (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ q.2.isLt))) ▸ small

end YM.Integration.WilsonGeometricSignedPrimary
