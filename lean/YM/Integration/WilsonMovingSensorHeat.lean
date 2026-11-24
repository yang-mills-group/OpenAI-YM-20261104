import YM.Integration.WilsonMovingSensorReserve

/-! Bound the true winding coefficient by its admitted age on the original
model. The finite sensor circumference remains independent of the regulator. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingSensorHeat
open Function Filter Lattice RG Wilson Precision Laurent Bloch Next.Foundations WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Blue
open scoped Classical Topology BigOperators

open FullVolume WilsonCoeffUV.Winding
open scoped Classical BigOperators
open Laurent Bloch

/-- The same admitted width controls both the spatial rate and the full
sum of aliased upper actions appearing in the formal sensor estimate. -/
theorem wind (r:ℕ) (U:Credit) : ∃ (C:ℝ) (k:ℕ), 0<C ∧
    ∀ {s y:ℝ}, 0<s → 1≤y → (perchA s r)⁻¹≤y →
      0<windPay s (U.buy y) r ∧ windPay s (U.buy y) r ≤ C*y^k := by
  let k:=Fintype.card (Fin r × Axis)
  let C:=3*U.x*4^k
  have u0:0<U.x:=lt_of_lt_of_le zero_lt_one U.good
  refine ⟨C,U.d+k,by dsimp [C];positivity,?_⟩
  intro s y hs hy paid
  have yp:0<y:=lt_of_lt_of_le zero_lt_one hy
  let t:=hingeZ s r
  have ht:0<t:=hinge_paid hs r
  have pw:0<perchA s r:=perch_pos hs r
  have up:perchA s r≤t:= (min_le_right _ _).trans (by linarith)
  have inv:t⁻¹≤y:=(inv_anti₀ pw up).trans paid
  have scale : 2*((1+t)/t)≤4*y := by rw [add_div,one_div,div_self ht.ne'];linarith
  have h:hinges s r≤(4*y)^k := pow_le_pow_left₀ (by dsimp [t] at ht ⊢;positivity) scale k
  have bill:0<U.buy y := lt_of_lt_of_le zero_lt_one (U.purchase hy)
  have power:1≤(4*y)^k:=one_le_pow₀ (by linarith)
  refine ⟨?_,?_⟩
  · dsimp only [windPay];have hh:=hinge_reserve hs r;positivity
  · calc windPay s (U.buy y) r ≤ U.buy y*((4*y)^k+1)+U.buy y := by
           dsimp only [windPay];gcongr
         _ ≤ 3*(U.buy y)*(4*y)^k := by nlinarith [mul_le_mul_of_nonneg_left power bill.le]
         _ = C*y^(U.d+k) := by dsimp [C,Credit.buy];rw [mul_pow,pow_add];ring

end YM.Integration.WilsonMovingSensorHeat
end
