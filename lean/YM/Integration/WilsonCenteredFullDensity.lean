import YM.Integration.WilsonCenteredHardFiled
import YM.Integration.WilsonCenteredSignedCapture

/-! The six physical sources in the absolute ordinary AB-minus-C moment
on the complete original receiving gallery. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredFullDensity
open Finset RG Lattice Wilson Marker QuadraticLocal Ac Source Labels
open Extra.Trajectories Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V] {R : Census V} {o : V→Site n}
    {P : Rep G n} (A : Gallery X ι o P R) (a b c : V) (s : R.Mode)

theorem original (apart : a≠b) (pair : s.val={a,b}) (x : X) (U : Config G n)
    (regular : Summable (fun j=>A.E.frame j x U))
    (hard : Summable (Fusion.Attached.packet P.activities P.p (A.K.hard x) U)) :
    (A.density x U).part s-(A.density x U).part (R.fire c)=
      (P.eval U:ℂ)*((A.E.log x U).part s)-(P.eval U:ℂ)*((A.E.log x U).part (R.fire c))+
      (P.eval U:ℂ)*((A.E.log x U).part (R.fire a)*(A.E.log x U).part (R.fire b))+
      (Real.exp (P.exponent U):ℂ)*((A.E.log x U).part (R.fire a)*(A.gas x U).part (R.fire b))+
      (Real.exp (P.exponent U):ℂ)*((A.E.log x U).part (R.fire b)*(A.gas x U).part (R.fire a))+
      (Real.exp (P.exponent U):ℂ)*((A.gas x U).part s-(A.gas x U).part (R.fire c)) := by
  let L:=A.E.log x U
  have zero : L.part R.quiet=0:=Lamps.quiet_of_hasSum x U regular
  have noMark := Hard.packet_of_quiet A.K x U hard
  change (A.gas x U).part R.quiet=(P.activities.gas P.p U:ℂ) at noMark
  have primary (j : V) : (Poly.pass L).part (R.fire j)=L.part (R.fire j) := by
    rw [←lamp j _ (Poly.pass_part L zero),connected_pass zero]
  have pairRow := twins a b s (Poly.pass L) (Poly.pass_part L zero) apart pair
  rw [connected_pass zero,primary a,primary b] at pairRow
  have complete:=WilsonCenteredHardPartitions.multiply a b c s apart pair (Poly.pass L) (A.gas x U)
  simp only [WilsonCenteredHardPartitions.face,primary,Poly.pass_part L zero,one_mul] at complete
  simp only [Gallery.density,Poly.part_smul,←mul_sub]
  rw [complete,noMark,Rep.eval,Complex.ofReal_mul]
  dsimp [L] at *
  linear_combination -(Real.exp (P.exponent U):ℂ)*(P.activities.gas P.p U:ℂ)*pairRow

end YM.Integration.WilsonCenteredFullDensity
