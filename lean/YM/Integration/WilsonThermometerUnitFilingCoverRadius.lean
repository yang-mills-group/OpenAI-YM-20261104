import YM.Integration.WilsonThermometerUnitFilingCoverRoom

/-! Price the native edge-midpoint support by the actual selected copy's joint trace. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverRadius
open Function Finset Lattice Gauge RG RegulatorIR Prim QuadraticLocal Stationary
open WilsonOriginalSuspendedFootprint WilsonOriginalCenteredSeamSalary WilsonEmittedRootedJetWage
open WilsonThermometerUnitFilingCoverRoom WilsonThermometerUnitFilingJointMonomial
open scoped Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{N:Side}{S:Finset Cover}(included:WilsonThermometerUnitFilingCoverChart.Centered N S)
  (p:Site N)
local notation "P"=>WilsonThermometerUnitFilingCoverChart.patch G S
local notation "route"=>WilsonThermometerUnitFilingCoverPort.branch included p G

def deposit {k:ℕ}(z:Fin k→Option (↥(P))):ℕ:=
  radius p (trace (Option.map (route) ∘ z) ∪ {p})

theorem placed {k:ℕ}(z:Fin k→Option (↥(P)))(i:Fin (length z)):
    mass (name z i).val.1.1 ≤ 4*deposit included p z:=by
  let x:=name z i
  have seen:z ((layout z i).val)=some x:= (Option.some_get (Finset.mem_filter.mp (layout z i).property).2).symm
  have present:((route) x).1∈trace (Option.map (route) ∘ z):=by
    apply Finset.mem_biUnion.mpr
    refine ⟨(layout z i).val,Finset.mem_univ _,?_⟩
    simp [Function.comp_apply,seen]
  have paid:separation p ((route) x).1≤deposit included p z:=
    Finset.le_sup (f:=separation p) (Finset.mem_union_left _ present)
  rw [separation_comm] at paid
  change pdist (wrap N x.val.1.1 + p - p) ≤ deposit included p z at paid
  rw [add_sub_cancel_right] at paid
  have site:x.val.1.1∈S:=(Finset.mem_product.mp (Finset.mem_product.mp x.property).1).1
  have liftback:lift (wrap N x.val.1.1)=x.val.1.1:=
    lift_eq_iff.mpr ⟨rfl,included _ site⟩
  change (∑ d:Axis,(x.val.1.1 d).natAbs)≤_
  calc
    _ ≤ ∑ _:Axis,deposit included p z:=by
      apply Finset.sum_le_sum;intro d _
      have h:=component_le (wrap N x.val.1.1) d
      rw [liftback] at h;exact h.trans paid
    _ = 4*deposit included p z:=by simp

theorem pricing {k u:ℕ}(z:Fin k→Option (↥(P))):
    wage u (length z) (name z) ≤
      (3+8*(k:ℝ))^u * (1+2*(deposit included p z:ℝ))^u:=by
  have count : length z≤k:=by
    simpa [length,live] using (Finset.card_filter_le (s:=Finset.univ) (p:=fun i:Fin k=>(z i).isSome))
  have paid: (∑ i,(mass (name z i).val.1.1:ℝ))≤ (k:ℝ)*(4*(deposit included p z:ℝ)):=by
    calc
      _ ≤ ∑ _:Fin (length z),(4*(deposit included p z:ℝ)):=by
        apply Finset.sum_le_sum;intro i _;exact_mod_cast placed included p z i
      _ = (length z:ℝ)*(4*(deposit included p z:ℝ)):=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right (by exact_mod_cast count) (by positivity)
  rw [← mul_pow]
  unfold wage reach
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [Nat.cast_nonneg (α:=ℝ) k, Nat.cast_nonneg (α:=ℝ) (deposit included p z),
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) k) (Nat.cast_nonneg (α:=ℝ) (deposit included p z))]

end YM.Integration.WilsonThermometerUnitFilingCoverRadius
