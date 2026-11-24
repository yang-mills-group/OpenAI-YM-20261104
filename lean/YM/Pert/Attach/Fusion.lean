import YM.Pert.Attach.Delivery
import YM.Pert.Attach.Equation
import YM.Pert.Attach.Moving
import YM.Pert.Attach.Indicators

/-! Exact same density with a changed regular term and retention of RG fiber budgets; quantitative gas cap with a one-unit exponent reserve. This lemma assumes equality only under joint masks, so does not grant any high-order bound for the regular comparison. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG Finset Filter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge}

variable {A R:Activities G n} {P Q:BudgetPoint} {δa δr w:ℝ} (ha:A.Valid Q δa w) (hr:R.RegularFamily P) (ht:Q.threshold=P.threshold)
    (hb:R.EBound P δr)
    (hmotion:∀ s b,∃ (u:A.Moves s b) (v:R.Moves s b),u.ep=v.ep)
    (halign:∀ i U,Healthy P.threshold (foot A R i) U → R.E i U = A.E i U)
local notation "ξ" => readjust A R P.threshold
local notation "ψ" => attach A ξ P.threshold R
include ha ht in
lemma forced_at : A.ForcedFamily P := ⟨ha.forced.sym,ha.forced.symtest,ha.forced.meas,ha.forced.meas_test,ht ▸ ha.forced.reads,
    ht ▸ ha.forced.reads_test,ht ▸ ha.forced.permit⟩

variable {q γ:ℝ} (hp : Prices A (readjust A R P.threshold) P q γ)
include ha hr ht hb hmotion halign hp

-- For infinite mask families, both products and logs here are genuine unweighted convergent sums, not logs of a presumed positive gas.
lemma fusion : (ψ).Valid P δr ((Real.exp γ-1)/q) ∧ ∀ U,
    Real.exp (-(ψ).additive P U)*(ψ).gas P U = Real.exp (-A.additive Q U)* A.gas Q U := by
   have h' := authorized ha hr ht hmotion halign
   have he : (ψ).Valid P δr ((Real.exp γ-1)/q) := ⟨⟨hr.smooth,hr.at_flat,hr.vanish⟩,forced (forced_at ha ht) h',fun s b=>
      (hmotion s b).elim fun u h=> h.elim fun v _ => ⟨moving u v (h'.move s b).some⟩,hb,bound A _ R P hp⟩
   refine ⟨he,fun U=>?_⟩
   have hx : A.regularOccurrence Q = A.regularOccurrence P := by unfold Activities.regularOccurrence; rw [ht]
   have hz : (ξ).value =(fun j U=> Real.exp (shiftLog A R P.threshold j U)-1) := rfl
   have hd i : shiftLog A R P.threshold i U = R.regularOccurrence P i U - A.regularOccurrence Q i U := by rw [hx]; rfl
   have hs₁ : Summable fun i=>A.regularOccurrence Q i U := (Activities.ESeries ha).summable U
   have hs₂ : Summable fun i=> R.regularOccurrence P i U := (Activities.ESeries he).summable U
   have hs : Summable (shiftLog A R P.threshold · U) := by simp_rw [hd]; exact hs₂.sub hs₁
   have hu : Summable (‖(ξ).value · U‖) := by
      rw [hz]; apply Summable.of_norm_bounded_eventually_nat ((hs.norm).mul_left 2)
      have hx :=hs.tendsto_atTop_zero.norm.eventually_le_const (show ‖(0:ℝ)‖<1 by simp)
      filter_upwards [hx] with i hi
      simp only [Real.norm_eq_abs,abs_abs]
      exact Real.abs_exp_sub_one_le (by simpa using hi)
   rw [total_gas ht ha h' U hu]
   rw [hz,show (fun j=>1+(Real.exp (shiftLog A R P.threshold j U)-1))=(fun j=>Real.exp (shiftLog _ _ _ j U)) from funext fun j=>by ring]
   have heq : (∏' j,Real.exp (shiftLog A R P.threshold j U)) = Real.exp (∑' j, shiftLog A R P.threshold j U) := by
      have hz := Real.hasProd_of_hasSum_log (fun i=> Real.exp_pos (shiftLog A R P.threshold i U))
        (a:=∑' i,shiftLog A R P.threshold i U)
      simp only [Real.log_exp] at hz
      exact (hz hs.hasSum).tprod_eq
   rw [heq,show ∑' j, shiftLog _ _ _ j U = R.additive P U-A.additive Q U from by
     simp_rw [hd]; exact hs₂.tsum_sub hs₁]
   change Real.exp (-R.additive P U)*(A.gas Q U*Real.exp (R.additive P U-A.additive Q U))=_
   rw [mul_left_comm,← Real.exp_add]; rw [show -R.additive P U+(R.additive P U-A.additive Q U) = -A.additive Q U by ring]
   exact mul_comm ..
end YM.Pert.Attach
