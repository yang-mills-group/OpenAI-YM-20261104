import YM.Integration.WilsonIndependentSpoutThermalLog
import YM.Integration.WilsonIndependentSpoutKineticReading

/-! Compose the actual unmarked reporting clocks at two adjacent dates of
one previously chosen upper history. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentSpoutChronologicalClock
open PowerSeries WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Power
open Precision Lattice Exterior FreeResolvent RG Tree Work.F08 AnalyticNext.QuarticMatch.Sheets
open scoped Classical BigOperators
variable {U:Type}

theorem compose (A B:Cost)(ha:constantCoeff A=1)(hb:constantCoeff B=1):
    (redo (U:=U) B).comp (redo A)=redo (chartB A B):=by
  let C:=chartB A B
  have hC:constantCoeff C=1:=cc_chart ha hb
  have hA:A*A⁻¹=1:=PowerSeries.mul_inv_cancel _ (by rw [ha];simp)
  have hB:B*B⁻¹=1:=PowerSeries.mul_inv_cancel _ (by rw [hb];simp)
  have h₁:C*(reel B A⁻¹*B⁻¹)=1:=by
    change reel B A*B*(reel B A⁻¹*B⁻¹)=_
    calc _=reel B (A*A⁻¹)*(B*B⁻¹):=by rw [map_mul];ring
         _=1:=by rw [hA,hB,map_one,one_mul]
  have refund:reel B A⁻¹*B⁻¹=C⁻¹:=by
    calc _=(C⁻¹*C)*(reel B A⁻¹*B⁻¹):=by rw [PowerSeries.inv_mul_cancel _ (by rw [hC];simp),one_mul]
         _=C⁻¹:=by rw [mul_assoc,h₁,mul_one]
  have hx:((redo (U:=U) B).comp (redo A)) X=soil C*X:=by
    rw [RingHom.comp_apply,redo_X,map_mul,WilsonIndependentSpoutThermalLog.cash,redo_X,
      ←mul_assoc,←map_mul]
    rfl
  apply serial_ext (by rw [hx];simp) _ (hx.trans (redo_X C).symm)
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [show PowerSeries.C (MvPolynomial.C a:POL U)=realS a from rfl,
      RingHom.comp_apply,redo_base,redo_base,redo_base]
  | add p q a b => simp only [map_add,a,b]
  | mul_X p j a =>
    rw [map_mul,map_mul,map_mul,a,show PowerSeries.C (MvPolynomial.X j:POL U)=path j from rfl,
      RingHom.comp_apply,redo_path,map_mul,WilsonIndependentSpoutThermalLog.cash,redo_path,redo_path,
      show soil (U:=U) ((reel B) A⁻¹) * (soil B⁻¹ * path j) = soil C⁻¹ * path j by
        rw [←mul_assoc,←map_mul,refund]]

private theorem even_chart {A B:Cost}(pa:evenC A)(pb:evenC B):evenC (chartB A B):=by
  intro i odd
  rw [chart_coeff]
  refine Finset.sum_eq_zero fun j hj=>?_
  have n:=Finset.mem_range.mp hj
  by_cases h:j%2=0
  · rw [even_pow pb (j+1) (i-j) (by omega),mul_zero]
  · rw [pa j h,zero_mul]

variable {G:Gauge}(A:Levels G)(Ñ:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio Ñ)

include simple ratio

theorem parity {N m k:ℕ}(hit:m+k≤N):evenC (relativeC A Ñ N m k):=by
  induction k with
  | zero=>exact even_one
  | succ k ih=>
    apply even_chart (ih (by omega))
    exact even_pace (angle_tilt simple ratio (by omega))
      (perch A Ñ simple ratio (by omega)).parityC

theorem turn {N m k:ℕ}(hit:m+(1+k)≤N):
    chartB (ratioHigh A Ñ N m) (relativeC A Ñ N m (1+k))=relativeC A Ñ N (m+1) k:=by
  rw [stageC,←chart_assoc]
  have h:relativeC A Ñ N m 1=pace (pitch A Ñ N m):=by simp [relativeC,leeB]
  rw [h,ratioHigh,chart_forward (angle_tilt simple ratio (by omega)),chart_ones]

theorem original {N m k:ℕ}(hit:m+(1+k)≤N)(p:Ink U):
    redo (relativeC A Ñ N m (1+k)) (redo (ratioHigh A Ñ N m) p)=
      redo (relativeC A Ñ N (m+1) k) p:=by
  have h:constantCoeff (ratioHigh A Ñ N m)=1:=back_cc (angle_tilt simple ratio (by omega))
  have g:constantCoeff (relativeC A Ñ N m (1+k))=1:=angularC simple ratio hit
  rw [←RingHom.comp_apply,compose (U:=U) (ratioHigh A Ñ N m) (relativeC A Ñ N m (1+k)) h g,
    turn A Ñ simple ratio hit]

end YM.Integration.WilsonIndependentSpoutChronologicalClock
