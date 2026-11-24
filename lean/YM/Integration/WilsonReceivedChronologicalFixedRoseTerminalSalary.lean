import YM.Integration.WilsonReceivedChronologicalFixedRoseFittedCurrency
import YM.Integration.WilsonOriginalTwoFlatIRSocketPower
import YM.Integration.WilsonOriginalOpticalCouplingBand

/-! Price the genuine complete packet sum against the actual older coupling at its filed terminal. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalFixedRoseTerminalSalary
open Function Filter Finset Lattice Wilson RG Pert.Asymptotics PhysicalNext.Repeat.Legato
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){n:ℕ}

private theorem cancel {x:ℝ}(xp:0<x)(a b e:ℕ)(order:a+b≤e):
    (x⁻¹)^a*(x⁻¹)^b*x^e=x^(e-(a+b)):=by
  have sum:a+b+(e-(a+b))=e:=by omega
  calc _ = (x^(a+b))⁻¹*x^(a+b+(e-(a+b))):=by rw [sum,←pow_add,inv_pow]
       _ = _:=by rw [pow_add x (a+b) (e-(a+b)),←mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ xp.ne'),one_mul]

include simple in
theorem original (d:Fin n→ℕ)(s:Finset (Fin n))(p E count bank mesh h goal target:ℕ)(C B:ℝ)
    (bp:0≤B)(order:target+1+bank+(mesh*h+1)≤goal):
    ∀ᶠv:ℕ in atTop,∀{N per K:ℕ},v≤N → ∀w:(i:Fin n)→R.family.label (d i),∀r:ℝ,0≤r →
    let g:=regulatorRun R.family N per v
    let cash:=∑q:Columns R (fun i:s=>d i.val),‖packet R d s w N per K q‖
    r^h*cash≤B*(g⁻¹)^bank*(g⁻¹)^(mesh*h+1) →
    r^h*((cash*WilsonOlderFreshSoftSocketCensus.fee R d s)*
      (g^goal*WilsonOriginalTwoFlatIRSocketPower.ceiling n p (∑i,d i) E count C))≤g^target:=by
  let fee:=WilsonOlderFreshSoftSocketCensus.fee R d s
  let cap:=WilsonOriginalTwoFlatIRSocketPower.ceiling n p (∑i,d i) E count C
  let bill:=|fee*cap|
  have bn:0≤bill:=abs_nonneg _
  filter_upwards [WilsonOriginalOpticalCouplingBand.cold R simple (max 2 (B*bill))]
    with v desk N per K vn w r rp
  let g:=regulatorRun R.family N per v
  let cash:=∑q:Columns R (fun i:s=>d i.val),‖packet R d s w N per K q‖
  change r^h*cash≤B*(g⁻¹)^bank*(g⁻¹)^(mesh*h+1) → r^h*((cash*fee)*(g^goal*cap))≤g^target
  intro earned
  have gp:0<g:=ActualRunKernelPackets.regulator_pos R N per v vn
  have posted:=desk N per vn
  have small:g≤1:=by
    have x:2≤g⁻¹:=(le_max_left ..).trans posted
    have one:1≤g⁻¹:=by linarith only [x]
    simpa [gp.ne'] using mul_le_mul_of_nonneg_right one gp.le
  have pay:B*bill*g≤1:=(mul_le_mul_of_nonneg_right ((le_max_right ..).trans posted) gp.le).trans_eq
    (inv_mul_cancel₀ gp.ne')
  have cash0:0≤cash:=sum_nonneg fun _ _=>norm_nonneg _
  have money:0≤r^h*cash*g^goal:=mul_nonneg (mul_nonneg (pow_nonneg rp _) cash0) (pow_nonneg gp.le _)
  have gain:(g⁻¹)^bank*(g⁻¹)^(mesh*h+1)*g^goal≤g^(target+1):=by
    rw [cancel gp bank (mesh*h+1) goal (by omega)]
    exact pow_le_pow_of_le_one gp.le small (by omega)
  calc r^h*((cash*fee)*(g^goal*cap)) = r^h*cash*g^goal*(fee*cap):=by ring
       _ ≤ r^h*cash*g^goal*bill:=mul_le_mul_of_nonneg_left (le_abs_self _) money
       _ ≤ (B*(g⁻¹)^bank*(g⁻¹)^(mesh*h+1))*g^goal*bill:=
         mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right earned (pow_nonneg gp.le _)) bn
       _ = B*bill*((g⁻¹)^bank*(g⁻¹)^(mesh*h+1)*g^goal):=by ring
       _ ≤ B*bill*g^(target+1):=mul_le_mul_of_nonneg_left gain (mul_nonneg bp bn)
       _ = (B*bill*g)*g^target:=by rw [pow_succ];ring
       _ ≤ 1*g^target:=mul_le_mul_of_nonneg_right pay (pow_nonneg gp.le _)
       _ = _:=one_mul _

end YM.Integration.WilsonReceivedChronologicalFixedRoseTerminalSalary
