import YM.Integration.WilsonPhysicalCentralInversion

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace YM.Integration.WilsonPhysicalCentralPolynomial
open Labels
open WilsonPhysicalCentralInversion
open scoped BigOperators
variable {G:Gauge}

theorem coordinate (J:Jet G)(k:Key G):
    coord (changedJet (fun j=>Taylor.turn (j:=j) flip⁻¹) J) k =
      (-1:ℂ)^(generation k)*coord J k:=by
  rcases k with ⟨j,a⟩
  simp [coord,changedJet,generation,inverse,turns]

theorem multiplier (m:Key G→₀ℕ):
    m.prod (fun i n=>(((-1:ℂ)^generation i)^n))=(-1:ℂ)^(height m):=by
  classical
  simp only [Finsupp.prod,←pow_mul,Finset.prod_pow_eq_pow_sum,height,Finsupp.weight_apply,
    Finsupp.sum,nsmul_eq_mul,Nat.mul_comm]
  simp

theorem monomial (m:Key G→₀ℕ)(a:ℂ):
    rotated flip (MvPolynomial.monomial m a)=MvPolynomial.monomial m (((-1:ℂ)^height m)*a):=by
  apply eval_ext
  intro J
  rw [rotated,eval_changed]
  simp only [Labels.read,MvPolynomial.aeval_monomial,Algebra.algebraMap_self_apply,coordinate,mul_pow]
  rw [Finsupp.prod_mul, multiplier]
  ring

theorem coefficient (p:Pol G)(k:Key G→₀ℕ):
    MvPolynomial.coeff k (rotated flip p)=(-1:ℂ)^(height k)*MvPolynomial.coeff k p:=by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [map_sum,monomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  by_cases h:k∈p.support
  · simp [h]
  · simp [h,MvPolynomial.notMem_support_iff.mp h]

theorem even_lower (p:Label G 5)(fixed:rotated flip p.val=p.val):
    ∃q:Label G 4,q.val=p.val:=by
  classical
  refine ⟨⟨p.val,?_,p.property.2⟩,rfl⟩
  apply (MvPolynomial.mem_restrictSupport_iff ℂ).mpr
  intro m hm
  have cap:height m≤5:=(MvPolynomial.mem_restrictSupport_iff ℂ).mp p.property.1 hm
  change height m≤4
  by_contra! above
  have top:height m=5:=by omega
  have e:=coefficient p.val m
  rw [fixed,top] at e
  norm_num at e
  exact (MvPolynomial.mem_support_iff.mp hm) (by linear_combination (1/2:ℂ)*e)

end YM.Integration.WilsonPhysicalCentralPolynomial
