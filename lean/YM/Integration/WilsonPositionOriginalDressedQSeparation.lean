import YM.Integration.WilsonPositionOriginalDressedQPayout
import YM.Corona.Fit
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDressedQSeparation
open Lattice Wilson RG Marker QuadraticLocal RG3 RG3.Letters
open WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[DecidableEq V]
variable {P:BudgetPoint}{o:V→Site n}{R:Census V}(L:Lamps T I G P o R)
variable {B m:ℕ}{w:V→ℝ}{α d:ℝ}

theorem original (hw:∀v,0<w v)(ha:0 ≤ α)(paid:Gross L w B α d)
    (s:R.Mode)(v u:V)(hv:v∈s.val)(hu:u∈s.val)
    (sep:m*(4*B+2)+2*B ≤ separation (o v) (o u))(t:T)(U:Config G n):
    ‖(bare L t U).part s‖ ≤ (Poly.toll w s*Real.exp (α*m))⁻¹*d:=by
  classical
  obtain ⟨f,pos,major,hit⟩:=paid.before
  let cost i:=if o v∈L.ground i then
    Poly.toll w (L.mode i)*f i*Real.exp (α*(coverNumber B (L.ground i):ℝ)) else 0
  have wallet:SumBudget cost d:=hit (o v)
  let atom i:=(Poly.send (L.mode i) (L.nominal t i U)).part s
  let k:=Poly.toll w s*Real.exp (α*m)
  have kp:0<k:=mul_pos (Poly.worth hw s) (Real.exp_pos _)
  have each(i):‖atom i‖ ≤ k⁻¹*cost i:=by
    unfold atom
    by_cases eq:L.mode i=s
    · have iv:o v∈L.ground i:=L.roots i v (eq ▸ hv)
      have iu:o u∈L.ground i:=L.roots i u (eq ▸ hu)
      have geo:=sep.trans (Corona.extent (L.ground i) B iv iu)
      have len:m ≤ coverNumber B (L.ground i):=by
        by_contra! contra
        have small:=Nat.mul_lt_mul_of_pos_right contra (show 0<4*B+2 by omega)
        omega
      have ht:Real.exp (α*m) ≤ Real.exp (α*(coverNumber B (L.ground i):ℝ)):=by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast len) ha
      rw [eq,Poly.part_send,if_pos rfl]
      change _ ≤ k⁻¹*(if o v∈L.ground i then _ else _)
      rw [if_pos iv,eq,←div_eq_inv_mul]
      apply (le_div_iff₀ kp).mpr
      unfold k
      calc ‖L.nominal t i U‖*(Poly.toll w s*Real.exp (α*m))=
            (Poly.toll w s*‖L.nominal t i U‖)*Real.exp (α*m):=by ring
           _ ≤ (Poly.toll w s*f i)*Real.exp (α*(coverNumber B (L.ground i):ℝ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left (major i t U) (Poly.worth hw s).le) ht
                (Real.exp_pos _).le (mul_nonneg (Poly.worth hw s).le (pos i))
    · rw [Poly.part_send,if_neg (Ne.symm eq),norm_zero]
      exact mul_nonneg (inv_nonneg.mpr kp.le) (wallet.1 i)
  have meters:Summable (fun i=>k⁻¹*cost i):=wallet.2.1.mul_left _
  have sums:Summable (fun i=>‖atom i‖):=Summable.of_nonneg_of_le (fun i=>norm_nonneg _) each meters
  unfold WilsonRootedKioskOccupiedSlip.bare
  by_cases terms:Summable (fun i=>Poly.send (L.mode i) (L.nominal t i U))
  · rw [Poly.share terms]
    change ‖∑' i,atom i‖ ≤ k⁻¹*d
    calc ‖∑' i,atom i‖ ≤ ∑' i,‖atom i‖:=norm_tsum_le_tsum_norm sums
         _ ≤ ∑' i,k⁻¹*cost i:=sums.tsum_le_tsum each meters
         _ ≤ k⁻¹*d:=by rw [tsum_mul_left];exact mul_le_mul_of_nonneg_left wallet.2.2 (inv_nonneg.mpr kp.le)
  rw [tsum_eq_zero_of_not_summable terms,Poly.part_nil,norm_zero]
  exact mul_nonneg (inv_nonneg.mpr kp.le) (tsum_nonneg wallet.1|>.trans wallet.2.2)

end YM.Integration.WilsonPositionOriginalDressedQSeparation
