import YM.Integration.WilsonOriginalFiledHardRebill
import YM.Integration.WilsonOriginalAlternativeTrialFlatWallet
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialUnitExpense
open Lattice Wilson RG Tree Marker QuadraticLocal Push.AbsoluteSums
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V]
theorem lamps {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]{J:Marker.Census V}{o:V→Site n}{b:BudgetPoint}
    (E:Lamps T I G b o J){w:V→ℝ}{B:ℕ}{α cost:ℝ}(wp:∀v,0<w v)(earned:E.Paid w B α cost):
    E.Paid (fun v=>min 1 (w v)) B α cost:=by
  have price(v:V):0 < min 1 (w v):=lt_min zero_lt_one (wp v)
  obtain ⟨budget,nonneg,controls,spent⟩:=earned.budget
  refine ⟨budget,nonneg,controls,fun site=>budget_mono (spent site) ?_ ?_⟩
  · intro j;split <;> first | exact mul_nonneg (mul_nonneg (Poly.worth price _).le (nonneg _)) (Real.exp_nonneg _) | rfl
  · intro j;split
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Finset.prod_le_prod
        (fun j _=>(price j).le) (fun j _=>min_le_right 1 (w j))) (nonneg _)) (Real.exp_nonneg _)
    · rfl


omit [DecidableEq V] in
theorem clock {w w₀:V→ℝ}{H d:ℝ}{a:ℕ}(hp:1≤H)(positive:∀i,0<w₀ i)(dp:0≤d)
    (base:∀i,(w₀ i)⁻¹≤H^a)(field:∀i,(w i)⁻¹≤(w₀ i)⁻¹*Real.exp d):
    (∀i,(min 1 (w₀ i))⁻¹≤H^a) ∧
    (∀i,(min 1 (w i))⁻¹≤(min 1 (w₀ i))⁻¹*Real.exp d):=by
  constructor
  · intro i
    by_cases small:w₀ i≤1
    · simpa only [min_eq_right small] using base i
    · rw [min_eq_left (le_of_not_ge small),inv_one]
      exact one_le_pow₀ hp
  · intro i
    have ini:0 < min 1 (w₀ i):=lt_min zero_lt_one (positive i)
    by_cases small:w i≤1
    · rw [min_eq_right small]
      exact (field i).trans (mul_le_mul_of_nonneg_right
        ((inv_le_inv₀ (positive i) ini).2 (min_le_right ..)) (Real.exp_nonneg _))
    · rw [min_eq_left (le_of_not_ge small),inv_one]
      have one:1≤(min 1 (w₀ i))⁻¹:=by
        simpa only [inv_one] using (inv_le_inv₀ zero_lt_one ini).2 (min_le_left 1 (w₀ i))
      exact one_le_mul_of_one_le_of_one_le one (Real.one_le_exp dp)

end YM.Integration.WilsonOriginalAlternativeTrialUnitExpense
end
