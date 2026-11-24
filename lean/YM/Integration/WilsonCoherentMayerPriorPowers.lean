import YM.Integration.WilsonCoherentMayerPriorJet

/-! A stored signed power shifts the field degree, including the zeros below its true floor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorPowers
open Finset
open scoped Classical BigOperators

theorem assemble (z:ℤ)(b:ℕ)(upper:z≤(b:ℤ))(a:ℕ→ℂ)
    (low:∀j:ℕ,j<(-z).toNat→a j=0)(t:ℂ)(ht:t≠0):
    t^z*(∑j∈range (((b:ℤ)-z).toNat+1),t^j*a j)=
      ∑k∈range (b+1),t^k*(if z≤(k:ℤ) then a ((k:ℤ)-z).toNat else 0):=by
  by_cases pos:0≤z
  · lift z to ℕ using pos with z hz
    let m:=b-z
    have len:((b:ℤ)-(z:ℤ)).toNat=m:=by dsimp [m];omega
    have split:b+1=z+(m+1):=by dsimp [m];omega
    rw [len]
    conv_rhs => rw [split,Finset.sum_range_add]
    have nil:∑k∈range z,t^k*(if (z:ℤ)≤(k:ℤ) then a ((k:ℤ)-(z:ℤ)).toNat else 0)=0:=by
      apply Finset.sum_eq_zero
      intro k hk
      rw [if_neg (by have h:=Finset.mem_range.mp hk;omega),mul_zero]
    rw [nil,zero_add,Finset.mul_sum,zpow_natCast]
    apply Finset.sum_congr rfl
    intro k _
    rw [if_pos (by omega),show ((↑(z+k):ℤ)-(z:ℤ)).toNat=k by omega,pow_add,mul_assoc]
  · let d:=(-z).toNat
    have val:z=-(d:ℤ):=by dsimp [d];omega
    have len:((b:ℤ)-z).toNat+1=d+(b+1):=by dsimp [d];omega
    rw [len,Finset.sum_range_add]
    have nil:∑k∈range d,t^k*a k=0:=by
      apply Finset.sum_eq_zero
      intro k hk
      rw [low k (Finset.mem_range.mp hk),mul_zero]
    rw [nil,zero_add,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [if_pos (by omega),show ((k:ℤ)-z).toNat=d+k by omega,val,zpow_neg,zpow_natCast,pow_add]
    have inv:(t^d)⁻¹*(t^d)=1:=inv_mul_cancel₀ (pow_ne_zero _ ht)
    calc _=(t^d)⁻¹*(t^d) * (t^k*a (d+k)):=by ring
         _=_:=by rw [inv,one_mul]

end YM.Integration.WilsonCoherentMayerPriorPowers
