import YM.Integration.WilsonConditionalTaylorWheelTensors
import YM.Integration.WilsonConditionalTaylorWheelRawVacuum

/-! Removing only the field-independent component after the finite signed
Haar logarithm agrees on all remaining polynomial ranks. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelRawCenter
open FormalBulk08 Orb Jets Shore Lava Series PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {U:Type} [Fintype U]

def collected (A:Pap U):Pal ℝ U:=lop (rancho (-A))

theorem acquired (P:Pal ℝ U) (q:ℕ) (bounds:shellK q P) (pure:∀i,Pure (P i)) (A:Pap U) (w:PowerSeries ℝ)
    (bill:-Blue.flash P=A-soil w):lop P=collected A:=by
  have before:Blue.flash P= -A+soil w:=calc
    _= -(-Blue.flash P):=(neg_neg _).symm
    _= -(A-soil w):=congrArg Neg.neg bill
    _= -A+soil w:=by abel
  funext e r
  cases r with
  | zero => simp [collected,lop]
  | succ r=>
    simp only [collected,lop,if_neg (Nat.succ_ne_zero _)]
    rw [←WilsonConditionalTaylorWheelTensors.actual P q bounds pure e (r+1),before]
    change canyon (r+1) (coeff e (-A + Blue.soil w))=canyon (r+1) (coeff e (-A))
    simp only [map_add,Blue.soil,coeff_map]
    have h:marble (r+1) (MvPolynomial.C (coeff e w):MvPolynomial U ℝ)=0:=
      (marble_eq_zero_iff ..).mpr (MvPolynomial.homogeneousComponent_eq_zero _ _ (by simp))
    exact add_eq_left.mpr h

theorem causal {E:ℕ} {P Q:Pap U} (paid:Through E P Q) (e:ℕ) (atCap:e ≤ E):collected P e=collected Q e:=by
  funext r
  unfold collected lop
  split_ifs with zero
  · rfl
  · unfold rancho
    rw [map_neg,map_neg,paid e atCap]

end YM.Integration.WilsonConditionalTaylorWheelRawCenter
end
