import YM.Integration.WilsonOriginalAlternativeTrialScales

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeTrialCollateral
open Finset Filter Lattice Wilson RG Marker PhysicalNext PhysicalNext.Repeat Legato
open WilsonThermometerMixedCollarSubpower
open scoped Classical BigOperators Topology
variable {V:Type}[DecidableEq V][Fintype V]{J:Census V}

def reserve (K f:ℕ):ℕ:=8*(9*(K-f)+6)

omit [Fintype V] in
theorem original {n a K f:ℕ}{z Z H:ℝ}(zp:0≤z)(Zp:0≤Z)(range:Z≤2*z)(Hp:1≤H)
    (w upper:V→ℝ)(pos:∀v,0<w v)(actual:∀v,(w v)⁻¹≤(upper v)⁻¹*Real.exp ((9*((K-f:ℕ):ℝ)+6)*Z^3))
    (salary:∀v,(upper v)⁻¹≤H^a)(s:J.Mode)(count:s.val.card≤n):
    let E:=Real.exp ((n:ℝ)*(reserve K f:ℝ)*z^3)
    (Poly.toll w s)⁻¹≤H^(a*n)*E ∧ 1≤H^(a*n)*(E*Poly.toll w s):=by
  let k:=9*((K-f:ℕ):ℝ)+6
  let x:=Real.exp ((reserve K f:ℝ)*z^3)
  have kn:0≤k:=by dsimp [k];positivity
  have loss:k*Z^3≤(reserve K f:ℝ)*z^3:=by
    have grow:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Zp range 3) kn
    simpa only [reserve,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using grow.trans_eq (show k*(2*z)^3= (8*(9*((K-f:ℕ):ℝ)+6))*z^3 by dsimp [k];ring)
  have xp:1≤x:=Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg zp _))
  have caps:∀v,(w v)⁻¹≤H^a*x:=by
    intro v
    exact (actual v).trans (mul_le_mul (salary v) (Real.exp_le_exp.mpr loss) (Real.exp_nonneg _) (pow_nonneg (zero_le_one.trans Hp) _))
  have mult:(Poly.toll w s)⁻¹≤(H^a*x)^n:=by
    change (∏v∈s.val,w v)⁻¹≤_
    rw [←Finset.prod_inv_distrib]
    calc _ ≤ ∏_∈s.val,(H^a*x):=Finset.prod_le_prod (fun v _=>inv_nonneg.mpr (pos v).le) (fun v _=>caps v)
         _ = _ := by simp
         _ ≤ _ := pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le (one_le_pow₀ Hp) xp) count
  have total:(H^a*x)^n=H^(a*n)*Real.exp ((n:ℝ)*(reserve K f:ℝ)*z^3):=by
    rw [mul_pow,←pow_mul,←Real.exp_nat_mul]
    ring_nf
  have paid:=mult.trans_eq total
  refine ⟨paid,?_⟩
  have one:1≤(H^(a*n)*Real.exp ((n:ℝ)*(reserve K f:ℝ)*z^3))*Poly.toll w s:=by
    exact (inv_le_iff_one_le_mul₀ (Poly.worth pos s)).mp paid
  simpa only [mul_assoc] using one

end YM.Integration.WilsonOriginalAlternativeTrialCollateral
end
