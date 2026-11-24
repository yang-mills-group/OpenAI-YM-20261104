import YM.Integration.WilsonPositionProgramTrialPublicJointFirstScore
import YM.Integration.WilsonPositionProgramTrialPublicJointFirstReturn

/-! The second normalized thermal response of a change of registered fields on one finite Wilson vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSecondScore
open Gauge Lattice Wilson XSpace Next.Rank.Normal PowerSeries Finset
open XSpace WilsonPositionProgramTrialPublicJointFirstScore
open WilsonIndependentSpoutMasterOrbitClock (measure shares)
open scoped BigOperators PowerSeries
variable {P:XSpace.Period}(T:P.Tree)(G:Gauge)

theorem second {A:Type*}[CommSemiring A](u v:PowerSeries A):
    coeff 2 (u*v)=coeff 2 u*constantCoeff v+coeff 1 u*coeff 1 v+constantCoeff u*coeff 2 v:=by
  rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=>coeff i u*coeff j v) 2]
  simp [Finset.sum_range_succ,coeff_zero_eq_constantCoeff]
  ac_rfl

theorem clock (B:PowerSeries ℝ)(unit:constantCoeff B=1)(u:PowerSeries ℂ):
    coeff 2 (measure B u)=coeff 2 u+(coeff (R:=ℝ) 1 B:ℂ)*coeff 1 u:=by
  rw [shares]
  simp [Finset.sum_range_succ,coeff_zero_eq_constantCoeff,unit,mul_comm,add_comm]

local notation "expect" => blend (Bare.Q T G) 0
def firstWeight:=WilsonPositionProgramTrialPublicJointFirstScore.score T G
def secondWeight:=coeff 2 (Bare.weight T G)
def ground (A:Bare.Series T G):ℂ:=expect (constantCoeff A)
def incoming (A:Bare.Series T G):ℂ:=expect (coeff 1 A+firstWeight T G*constantCoeff A)
def next (A:Bare.Series T G):ℂ:=expect
  (coeff 2 A+firstWeight T G*coeff 1 A+secondWeight T G*constantCoeff A)

theorem raw (A:Bare.Series T G):coeff 2 (Bare.normalized T G A)=
    next T G A-expect (firstWeight T G)*coeff 1 (Bare.normalized T G A)-expect (secondWeight T G)*ground T G A:=by
  have h:=congrArg (coeff (R:=ℂ) 2) (Bare.normalize_denominator T G A)
  have v1:coeff 1 (Bare.vacuum T G)=expect (firstWeight T G):=by
    rw [Bare.vacuum,Bare.diagram_coeff,mul_one,firstWeight,active]
  have v2:coeff 2 (Bare.vacuum T G)=expect (secondWeight T G):=by
    rw [Bare.vacuum,Bare.diagram_coeff,mul_one];rfl
  rw [second,Bare.vacuum_start,mul_one,v1,v2,Bare.leading,Bare.diagram_coeff,second,Bare.weight_one,one_mul,active] at h
  unfold next ground
  rw [show coeff 2 A+firstWeight T G*coeff 1 A+secondWeight T G*constantCoeff A=
    coeff 2 (Bare.weight T G)*constantCoeff A+score T G*coeff 1 A+coeff 2 A from by unfold firstWeight secondWeight; ring,←h]
  ring

/-- When the two full ground fields agree, both pure second-vacuum terms cancel on this very tree. -/
theorem agreement (A B:Bare.Series T G)(same:constantCoeff A=constantCoeff B):
    coeff 2 (Bare.normalized T G A)-coeff 2 (Bare.normalized T G B)=
      expect (coeff 2 (A-B)+firstWeight T G*coeff 1 (A-B))-
        expect (firstWeight T G)*expect (coeff 1 (A-B)):=by
  rw [←map_sub,←map_sub,raw]
  have zero:constantCoeff (A-B)=0:=by rw [map_sub,same,sub_self]
  have one:coeff 1 (Bare.normalized T G (A-B))=expect (coeff 1 (A-B)):=by
    rw [(WilsonPositionProgramTrialPublicJointFirstScore.original T G (A-B)).2,zero]
    simp
  rw [one]
  simp only [next,ground,zero,mul_zero,add_zero,map_zero,sub_zero]

/-- The two occupations are rephased after taking their signed difference. -/
theorem reported (B:PowerSeries ℝ)(unit:constantCoeff B=1)(A D:Bare.Series T G):
    coeff 2 (measure B (Bare.normalized T G A))-coeff 2 (measure B (Bare.normalized T G D))=
      coeff 2 (Bare.normalized T G (A-D))+(coeff (R:=ℝ) 1 B:ℂ)*coeff 1 (Bare.normalized T G (A-D)):=by
  simp only [clock B unit,map_sub,mul_sub]
  ring

end YM.Integration.WilsonPositionProgramTrialPublicJointSecondScore
end
