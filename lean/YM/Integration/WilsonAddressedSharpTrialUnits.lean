import YM.Integration.WilsonAddressedTrialPivotUnits
import YM.Integration.WilsonReflectedMixedSharpAxis

/-! A grade-compensated received row can spend the actual preselected
physical inverse at its negotiated tolerance on every turn and grid point. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedSharpTrialUnits
open Finset Function Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato
open Extra.Histories Motion
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalPublicPivotRoster (Slot weight coord salaryOf)
open WilsonOriginalPublicFigureWick (project)
open WilsonOriginalPublicPivotWeights (Paid)
open WilsonAddressedTrialPivotUnits (ceiling row)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonOriginalMicroscopicGuardedReporters (stretch)
open scoped Classical BigOperators
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
local notation "a" => R.family.S.a
local notation "F" d:max => R.family.labels.level d

def fixed (d j f:ℕ)(η:ℝ)(t:ℂ)(salary:ℝ):ℝ:=
  4*‖t‖*(salaryOf W (F d)*(2:ℝ)^(Finset.univ.sup fun i:(F d).Index=>((F d).grades i).2))*
    orbitCost (F d)*salary*(a j/a f)^((d:ℝ)+η)

variable {d j f K N p target:ℕ}(before:j≤f)(up:f≤K)(live:K≤N){η:ℝ}
  (A:(R.family.label d)≃ₗ[ℂ](R.family.label d))(Y:R.family.label d) {salary:ℝ}
  (cash:Cash (R:=R) d j f K N p target before up live η A Y salary)
  (arm:Arm R d N p f K) (same:arm.w=A.symm (fitted R d j N p Y))

include cash same in
theorem billed (t:ℂ):
    ceiling R W d f t (coords R arm) ≤ fixed R W d j f η t salary*(a f/a K)^η:=by
  have aj:=R.family.S.a_pos j
  have af:=R.family.S.a_pos f
  have ak:=R.family.S.a_pos K
  have time:R.family.S.scale K-R.family.S.scale j=Real.log (a j/a K):=by
    rw [Schedule.scale,Schedule.scale,Real.log_inv,Real.log_inv,Real.log_div aj.ne' ak.ne']
    ring
  have phase:stretch R η j K=2*(a j/a K)^η:=by
    unfold WilsonOriginalMicroscopicGuardedReporters.stretch
    rw [Real.rpow_def_of_pos (div_pos aj ak),←time,mul_comm η]
  have split:(a j/a K)^η=(a j/a f)^η*(a f/a K)^η:=by
    rw [←Real.mul_rpow (div_pos aj af).le (div_pos af ak).le]
    congr 1
    field_simp
  have unturned:(F d).coeffSize arm.w ≤ stretch R η j K*(2*(a j^d*salary)):=by
    rw [same]
    exact cash.2.1
  have op:0≤orbitCost (F d):=zero_le_one.trans (orbitCost_one_le _)
  have measured:= (patch_cost (F d) (arm.s,arm.b) arm.w).trans (mul_le_mul_of_nonneg_left unturned op)
  change (F d).coeffSize (coords R arm) ≤ _ at measured
  have book:(0:ℝ)≤WilsonOriginalPublicPivotRoster.salaryOf W (F d):=
    Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  unfold ceiling fixed
  refine (mul_le_mul_of_nonneg_left measured (by positivity)).trans_eq ?_
  rw [phase,split,Real.rpow_add (div_pos aj af),Real.rpow_natCast,div_pow]
  ring

include cash same in
theorem original (t:ℂ)(U:Matrix Unit (Slot G d) ℂ){B:ℝ}(nn:0≤B)
    (paid:Paid (a K/a f) (fun _:Unit=>d) weight U B):
    let δ:=a K/a f
    let vK:=row R d K N p t (coords R arm)
    ‖∑b:Slot G d,U () b*((δ:ℂ)^weight b*coord (project W (F d) vK) b)‖ ≤
      B*(fixed R W d j f η t salary*(a f/a K)^η):=
  (WilsonAddressedTrialPivotUnits.transmitted R W d f K N p live t (coords R arm) U nn paid).trans
    (mul_le_mul_of_nonneg_left (billed R W before up live A Y cash arm same t) nn)

end YM.Integration.WilsonAddressedSharpTrialUnits
end
