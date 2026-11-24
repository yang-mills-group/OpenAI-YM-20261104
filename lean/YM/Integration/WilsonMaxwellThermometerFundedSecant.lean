import YM.Integration.WilsonThermometerCenteredScalar
import YM.Integration.WilsonFundedPositionConnected

/-! Seven-slot divided difference of the actual ordinary connected read.
The cofactor of each proper pair uses the independently filed singleton.
The coefficients of the singletons use the genuine physical proper pairs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerFundedSecant
open Finset Marker WilsonPositionThermometerConnected

open scoped Classical BigOperators
local notation "J₀"=>Stock.census (Fin 3)
local notation "Badge"=>Finset (Fin 3)

def faceKey : Fin 7→Badge := ![univ,{0,1},{0,2},{1,2},{0},{1},{2}]
def parcel (p q:Badge→ℂ):Fin 7→ℂ:=![1,-q {2},-q {1},-q {0},
  -p {1,2}+2*p {1}*p {2},-p {0,2}+2*q {0}*p {2},-p {0,1}+2*q {0}*q {1}]

def bill (p q:Badge→ℂ) (s:Badge):ℂ:=∑t:Fin 7,if s=faceKey t then parcel p q t else 0

private theorem transfer (p q h:Badge→ℂ):
    ∑s:Badge,bill p q s*h s=∑t:Fin 7,parcel p q t*h (faceKey t):=by
  simp only [bill,sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun t _=>?_
  simp [ite_mul]

/-- The exact two-correlation difference on the signed ordinary thermometer. -/
theorem signed (p q:Badge→ℂ):
    value p-value q=∑s:Badge,bill p q s*(p s-q s):=by
  rw [transfer]
  simp only [value,Fin.sum_univ_succ,Fin.sum_univ_zero,faceKey,parcel,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_fin_one,add_zero]
  ring

end YM.Integration.WilsonMaxwellThermometerFundedSecant
