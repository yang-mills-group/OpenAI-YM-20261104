import YM.Integration.WilsonPositionScaleLawMeasuredWord
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredWordExpansion
open Finset Function Filter Set PowerSeries Maxwell XSpace XSpace.Normalize
open WilsonPositionScaleLawMeasuredWord (Word weight node)
open scoped BigOperators Classical Topology
variable {G:Gauge}{d n:ℕ}

def digits (n q:ℕ) : Word n q ≃ Fin (q+1) × (Fin n→Fin (q+1)) where
  toFun w:=(w none,fun i=>w (some i))
  invFun p:=fun a=>a.elim p.1 p.2
  left_inv w:=by funext a;cases a <;> rfl
  right_inv p:=by cases p;rfl

def leg (T:Guard G d)(q:ℕ)(u:ℝ)(v:Sec G d) : Sec G d :=
  ∑j:Fin (q+1),(u:ℂ)^(j:ℕ) • coeff (j:ℕ) T v

theorem expanded (T:Guard G d)(R:Reports G d)(q:ℕ)(u:ℝ)(φ:Test n)(v:Fin n→Sec G d) :
    WilsonPositionScaleLawMeasuredWord.opened T R q u φ v=
      ∑k:Fin (q+1),(u:ℂ)^(k:ℕ)*R (k:ℕ) n φ (fun i=>leg T q u (v i)) :=by
  let W (p:Fin (q+1)×(Fin n→Fin (q+1))) := (u:ℂ)^(p.1.val+∑i,(p.2 i).val)*
    R p.1.val n φ (fun i=>coeff (p.2 i).val T (v i))
  have price:WilsonPositionScaleLawMeasuredWord.opened T R q u φ v=∑p,W p :=by
    rw [←Equiv.sum_comp (digits n q) W]
    apply sum_congr rfl
    intro x _
    simp only [W,digits,Equiv.coe_fn_mk,weight,Fintype.sum_option,node]
  rw [price,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro k _
  unfold leg
  rw [MultilinearMap.map_sum,mul_sum]
  apply sum_congr rfl
  intro b _
  rw [(R k.val n φ).map_smul_univ,smul_eq_mul,prod_pow_eq_pow_sum]
  dsimp only [W]
  rw [pow_add,mul_assoc]

theorem original (T:Guard G d)(R:Reports G d)(q:ℕ)(u:ℝ)(small:|u|≤1)(φ:Test n)(v:Fin n→Sec G d) :
    ‖(∑k:Fin (q+1),(u:ℂ)^(k:ℕ)*R (k:ℕ) n φ (fun i=>leg T q u (v i)))-
      WilsonPositionScaleLawMeasuredWord.clipped T R q u φ v‖ ≤
      |u|^(q+1)*∑w:Word n q,‖node T R φ v w‖ :=by
  rw [←expanded]
  exact WilsonPositionScaleLawMeasuredWord.error T R q u small φ v

end YM.Integration.WilsonPositionScaleLawMeasuredWordExpansion
