import YM.Integration.WilsonThermometerWeakNestedChild

/-! Account for both root remainders in the full ordinary moment. All signed
proper subwords stay inside the original parent before the triangle bound. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPairTriangle
open Finset Function OPE OPE.Arboreal
open scoped Classical BigOperators
variable {I J:Type}

theorem account (i:Finset I)(j:Finset J)(X:ℂ)(Y c:I→ℂ)(A v:J→ℂ)(B:I→J→ℂ):
    ‖X-∑u∈i,c u*Y u‖ ≤ ‖X-∑w∈j,A w*v w‖+
        ∑w∈j,‖A w-∑u∈i,c u*B u w‖*‖v w‖+
        ∑u∈i,‖c u‖*‖Y u-∑w∈j,B u w*v w‖:=by
  have transfer : ∑w∈j,∑u∈i,c u*B u w*v w = ∑u∈i,∑w∈j,c u*(B u w*v w):= by
    rw [sum_comm];simp only [mul_assoc]
  have amount:X-∑u∈i,c u*Y u=(X-∑w∈j,A w*v w)+
      (∑w∈j,(A w-∑u∈i,c u*B u w)*v w)-(∑u∈i,c u*(Y u-∑w∈j,B u w*v w)):=by
    simp_rw [sub_mul,mul_sub,sum_sub_distrib,sum_mul,mul_sum];rw [transfer];ring
  rw [amount]
  calc
    _≤(‖X-∑w∈j,A w*v w‖+‖∑w∈j,(A w-∑u∈i,c u*B u w)*v w‖)+
          ‖∑u∈i,c u*(Y u-∑w∈j,B u w*v w)‖:=
      (norm_sub_le ..).trans (add_le_add (norm_add_le ..) (le_refl _))
    _≤_:=by
      have left:=norm_sum_le j (fun w=>(A w-∑u∈i,c u*B u w)*v w)
      have right:=norm_sum_le i (fun u=>c u*(Y u-∑w∈j,B u w*v w))
      simp only [norm_mul] at left right
      exact add_le_add (add_le_add (le_refl _) left) right

end YM.Integration.WilsonThermometerWeakPairTriangle
end
