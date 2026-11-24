import YM.AllOrder.Fire.PriceR
import YM.Integration.WilsonMarkedHomogeneousJet
import YM.Integration.WilsonPhysicalLogChainPrice

/-! Finite scalar samples on the authentic retained-field ball control every
derivative on a fixed smooth test curve. The constants depend on its degree
and its test order, not on the dimension of the torus field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMarkedAngularTestInvoice
open Function Set Finset AllOrder.Fire PositionX.Jet Planned.AtomRegular Tensor PertExtension.Series
open scoped ContDiff Topology Classical

variable {X:Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem regular {d:ℕ}{f:X→ℝ}(h:Rank X d f)(k:WithTop ℕ∞):ContDiff ℝ k f:=by
  induction h with
  | nil=>exact contDiff_const
  | add _ _ ih ik=>exact ih.add ik
  | @dot P n f h ih=>exact P.contDiff.mul ih

def fee (d q:ℕ):ℝ:=polarCost q*((q.factorial:ℝ)*(analytic_cost d).choose)
theorem fee_nonnegative (d q:ℕ):0≤fee d q:=mul_nonneg (zero_le_one.trans (polar_one q))
  (mul_nonneg (Nat.cast_nonneg _) (analytic_cost d).choose_spec.1.le)

theorem linear {d q:ℕ}(hq:q≤d){f:X→ℝ}(h:Rank X d f){ε:ℝ}(pos:0≤ε)
    (bill:∀x,‖x‖≤(d:ℝ)→|f x|≤ε):
    ‖iteratedFDeriv ℝ q f 0‖≤fee d q*ε:=by
  let M:=(analytic_cost d).choose
  have M0:0≤M:=(analytic_cost d).choose_spec.1.le
  unfold fee
  rw [mul_assoc, mul_assoc]
  apply op_polar (Analysis.sym_Jet (regular h q).contDiffAt) (by positivity)
  intro y hy
  let L:ℝ→L[ℝ]X:=(ContinuousLinearMap.id ℝ ℝ).smulRight y
  have rankLine:Rank ℝ d (fun t:ℝ=>f (t • y)):=h.lead L
  have sample:(∀i:Fin (d+1),|f ((i.val:ℝ) • y)|≤ε):=by
    intro i
    apply bill
    rw [norm_smul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
    apply (mul_le_of_le_one_right (Nat.cast_nonneg _) hy).trans
    exact_mod_cast (Nat.le_of_lt_succ i.isLt)
  have price:‖someJ (fun t:ℝ=>f (t • y)) q‖≤M*ε:=
    (analytic_cost d).choose_spec.2 _ rankLine ε sample ⟨q,by omega⟩
  change ‖iteratedFDeriv ℝ q f 0 (fun _=>y)‖≤_
  have ray:=Radial.radial_iteratedDeriv (f:=f) y (0:ℝ) q isOpen_univ (Set.mem_univ _) (regular h q).contDiffOn
  simp only [zero_smul] at ray
  have recover:(q.factorial:ℝ)*someJ (fun t:ℝ=>f (t • y)) q=iteratedDeriv q (fun t:ℝ=>f (t • y)) 0:=by
    simp [someJ,smul_eq_mul,Nat.factorial_ne_zero]
  rw [←ray,←recover,norm_mul,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact mul_le_mul_of_nonneg_left price (Nat.cast_nonneg _)

end YM.Integration.WilsonMarkedAngularTestInvoice
end
