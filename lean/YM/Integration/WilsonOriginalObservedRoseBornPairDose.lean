import YM.Integration.WilsonOriginalObservedRoseCorrectedWords
import YM.Integration.WilsonOriginalPhysicalFruitDose

set_option autoImplicit false

noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornPairDose
open Finset Lattice RG Wilson Source Labels Extra.Histories Motion PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses units)
open WilsonPositionProgramReportedField (entire)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per K f:ℕ}
local notation "F" i:max => R.family.labels.level (d i)
local notation "a" => R.family.S.a

def restored (file:Filed R d K)(Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r:ℝ)(t:ℂ)(i:Fin n):(F i).Coeff:=fun b=>
  (((a K/r)^(d i):ℝ):ℂ)*t*((entire R (d i) K (N,per) (votes R d (N:=N) (per:=per) file Y turn i)) b)*
    (((regulatorRun R.family N per K)^((F i).grades b).2:ℝ)⁻¹:ℝ)

theorem original (file:Filed R d K)(Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r:ℝ)(t:ℂ)(i:Fin n):
    amounts R (d i) K N per r t
      (Motion.patch (F i) (turn i) (doses R d file.station (N:=N) (per:=per) (file.A N per) Y i)) =
      restored R d (N:=N) (per:=per) file Y turn r t i:=by
  classical
  let v:=Motion.patch (F i) (turn i) (doses R d file.station (N:=N) (per:=per) (file.A N per) Y i)
  have engineering:(t*(((a K:ℂ)^(d i))⁻¹)) • v=t • votes R d (N:=N) (per:=per) file Y turn i:=by
    dsimp only [votes, units]
    rw [smul_smul]
  funext b
  dsimp only [amounts,WilsonOriginalPublicTrialFigure.amount,WilsonAddressedTrialPivotUnits.row,restored]
  change (((a K/r)^(d i):ℝ):ℂ) *
      ((entire R (d i) K (N,per) ((t*(((a K:ℂ)^(d i))⁻¹)) • v)) b*_) = _
  rw [engineering]
  simp only [entire,map_smul,Pi.smul_apply,smul_eq_mul]
  ring

theorem arm (file:Filed R d K)(Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r:ℝ)(t:ℂ)(i:Fin n)
    (A:Arm R (d i) N per f K)
    (source:A.w=(file.A N per i).symm (fitted R (d i) (file.station i) N per (Y i)))
    (oriented:(A.s,A.b)=turn i):
    amounts R (d i) K N per r t (coords R A)=restored R d (N:=N) (per:=per) file Y turn r t i:=by
  rw [coords,oriented,source]
  exact original R d file Y turn r t i

end YM.Integration.WilsonOriginalObservedRoseBornPairDose
end

