import YM.Integration.WilsonOlderFreshSoftSocketHistory

/-! The transferred planting pole has its original multiplicity and its own dated kinetic unit. All positive degrees of this unit survive on the discharged scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketKinetic
open Function Finset Filter Lattice Wilson RG Laurent Bloch Precision PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Mer WilsonCoeffUV.Blue
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Power WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Fountain WilsonCoeffUV.Soil
open Work.F08 AnalyticNext.QuarticMatch.Sheets MultiNext.SignedSource Tree
open WilsonOlderFreshSoftCoverScalar (clock)
open scoped Classical BigOperators
variable {G:Gauge}

def kinetic (A:Levels G)(O:ChartRatio G)(N b m:ℕ):Cost:=
  if _:m<b then chartB (kinetic A O N b (m+1)) (ratioHigh A O N m) else 1
termination_by b-m

theorem pole (A:Levels G)(O:ChartRatio G)(N b m h:ℕ)(mb:m≤b):
    clock A O N b m (X^h)=X^h*(kinetic A O N b m)^h:=by
  induction mb using Nat.decreasingInduction with
  | self=>
    rw [clock,dif_neg (lt_irrefl b),kinetic,dif_neg (lt_irrefl b),one_pow,mul_one]
  | of_succ i hi ih=>
    conv_rhs=>rw [kinetic,dif_pos hi]
    rw [clock,dif_pos hi,ih,map_mul,map_pow,reel_X,map_pow,chartB]
    ring

theorem unit (A:Levels G)(O:ChartRatio G)(simple:G.Simple)(localO:LocalRatio O)
    (N b m:ℕ)(mb:m≤b)(bn:b≤N):constantCoeff (kinetic A O N b m)=1:=by
  induction mb using Nat.decreasingInduction with
  | self=>rw [kinetic,dif_neg (lt_irrefl b),map_one]
  | of_succ i hi ih=>
    rw [kinetic,dif_pos hi]
    have coin:constantCoeff (ratioHigh A O N i)=1:=back_cc (angle_tilt simple localO (hi.trans_le bn))
    have zero:=chart_coeff (kinetic A O N b (i+1)) (ratioHigh A O N i) 0
    simpa [coeff_zero_eq_constantCoeff,ih,coin] using zero

theorem combine (A:Levels G)(O:ChartRatio G)(N b c m:ℕ)(mc:m≤c)(cb:c≤b)(T:Cost):
    clock A O N c m (clock A O N b c T)=clock A O N b m T:=by
  induction mc using Nat.decreasingInduction with
  | self=>rw [clock,dif_neg (lt_irrefl c)]
  | of_succ i hi ih=>
    conv_lhs=>rw [clock,dif_pos hi]
    conv_rhs=>rw [clock,dif_pos (hi.trans_le cb)]
    rw [ih]

def reading {U:Type}(P:Pal ℝ U){r:ℕ}(v:Fin r→U):Cost:=PowerSeries.mk (fun j=>P j r v)

theorem valued {U:Type}(P:Pal ℝ U)(C:Cost){r:ℕ}(v:Fin r→U):
    reading (affix C P) v=C*reading P v:=by
  apply PowerSeries.ext
  intro e
  rw [reading,coeff_mk,coeff_mul]
  simp only [reading,coeff_mk,affix,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem discharged (A:Levels G)(O:ChartRatio G)(N b m h:ℕ)(mb:m≤b)
    {U:Type}(P:Pal ℝ U){r:ℕ}(v:Fin r→U)(e:ℕ):
    coeff (e+h) (reading (affix (clock A O N b m (X^h)) P) v)=
      coeff e ((kinetic A O N b m)^h*reading P v):=by
  rw [valued,pole A O N b m h mb,mul_assoc]
  simp [PowerSeries.coeff_X_pow_mul']

end YM.Integration.WilsonOlderFreshSoftSocketKinetic
end
