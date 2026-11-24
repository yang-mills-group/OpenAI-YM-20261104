import YM.Integration.WilsonThermometerUnitFilingFlatFaces
import YM.Integration.WilsonThermometerRegisteredCenteredFixedInvoice

/-! The same compensated finite ordinary table with the two affordable withdrawals of the measured singles. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatWithdrawal
open Function Finset Lattice Marker RG QuadraticLocal Extra.Trajectories Primitives.GCC.Anchor
open Comparison.RG02 Comparison.RG02.Order WilsonThermometerCenteredAlgebra WilsonThermometerRegisteredCenteredInvoice
open WilsonThermometerRegisteredCenteredFixedInvoice WilsonFiniteOrdinaryInverse WilsonThermometerCenteredScalar
open scoped BigOperators Classical
local notation "J" => Stock.census (Fin 3)
variable {w:Fin 3→ℝ} {g:ℝ} (pos:∀v,0<w v) (gp:0<g)

theorem full_width : Poly.toll (fun v=>g*w v) full=g^3*Poly.toll w full:=by
  simp [Poly.toll,full,Finset.prod_mul_distrib]

include pos gp in
theorem original (U Z F:Poly J) (loss:ℕ) (unscaled:g^(loss+2)≤Poly.toll w full)
    (capped:∀v,g*w v≤1) (means:∀v:Fin 3,‖read F {v}‖≤1) (cost:ℝ)
    (allFaces:∀Q:Poly J,Poly.toll (fun v=>g*w v) full*‖(total U Q).part full-(total Z Q).part full‖≤
      cost*Poly.price (fun v=>g*w v) (inverseMass Q)):
    ‖(U*properInvoice F 1).part full-(Z*properInvoice F 1).part full‖≤
      23*(|cost| *fee J/g^(loss+5)):=by
  let w':=fun v=>g*w v
  have funded:∀v,0<w' v:=fun v=>mul_pos gp (pos v)
  have width:g^(loss+5)≤Poly.toll w' full:=by
    rw [full_width]
    exact (show g^(loss+5)=g^3*g^(loss+2) by rw [←pow_add];congr 1;omega).le.trans
      (mul_le_mul_of_nonneg_left unscaled (pow_pos gp 3).le)
  obtain ⟨quiet,elected⟩:=affordable F w' funded capped means
  have pay (Q:Poly J) (paid:Poly.price w' (inverseMass Q)≤fee J):
      ‖(total U Q).part full-(total Z Q).part full‖≤|cost| *fee J/g^(loss+5):=by
    apply (le_div_iff₀ (pow_pos gp _)).mpr
    rw [mul_comm]
    exact ((mul_le_mul_of_nonneg_right width (norm_nonneg _)).trans (allFaces Q)).trans
      (mul_le_mul (le_abs_self _) paid (Poly.nonnegative funded _) (abs_nonneg _))
  have a:=pay _ elected
  have b:=pay _ quiet
  rw [reading F U,reading F Z]
  rw [show (12*(total U (tested F)).part full-11*(total U 1).part full)-
    (12*(total Z (tested F)).part full-11*(total Z 1).part full)=
    12*((total U (tested F)).part full-(total Z (tested F)).part full)-
    11*((total U 1).part full-(total Z 1).part full) by ring]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul]
  norm_num
  linarith only [a,b]

end YM.Integration.WilsonThermometerUnitFilingFlatWithdrawal
