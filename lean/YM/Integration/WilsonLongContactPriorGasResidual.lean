import YM.Integration.WilsonLongContactPriorGasSum

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonLongContactPriorGasResidual
open Lattice Wilson RG Marker Merge
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {V:Type} [DecidableEq V] {Γ:Census V}
  (A:Activities G n) (P:BudgetPoint) (w:V→ℝ) (f:ℕ→Poly Γ)
local notation "Y" => fun i=>(A.forced i).support

def empty (U:Config G n):Poly Γ:=if (flags P.threshold U).Nonempty then 0 else 1

theorem paid (hw:∀v,0<w v) (U:Config G n) (η:ℝ) (small:η≤1) (pos:0≤η)
    (income:∀(x:Site n)(L:Finset ℕ),∑i∈Ac.buds Y L {x},Poly.price w (f i)≤η):
    Poly.price w ((∑'s,Photo.fronts A f U P s)-empty P U)≤η:=by
  classical
  by_cases hx:(flags P.threshold U).Nonempty
  · simpa only [empty,if_pos hx,sub_zero] using (WilsonLongContactPriorGasSum.original A P w f hw U η small income).2.2.2
  have clean:=Finset.not_nonempty_iff_eq_empty.mp hx
  rw [WilsonLongContactPriorGasSum.cold A P f U clean,empty,if_neg hx,sub_self,Poly.zero_price]
  exact pos

theorem weighted (hw:∀v,0<w v) (β:ℂ) (reg gas clear:Poly Γ) (ε:ℝ) (price:Poly.price w (gas-clear)≤ε):
    Poly.price w (β • (reg*gas)-β • (reg*clear))≤ ‖β‖*Poly.price w reg*ε:=by
  rw [←smul_sub,←mul_sub,Poly.adapted,mul_assoc]
  exact mul_le_mul_of_nonneg_left ((Poly.multiplication hw reg (gas-clear)).trans
    (mul_le_mul_of_nonneg_left price (Poly.nonnegative hw reg))) (norm_nonneg _)

end YM.Integration.WilsonLongContactPriorGasResidual
