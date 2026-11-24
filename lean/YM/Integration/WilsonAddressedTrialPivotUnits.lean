import YM.Integration.WilsonAddressedFiniteThermalInput
import YM.Integration.WilsonOriginalPublicPivotRoster

/-! The scale in a deposited curvature coordinate and its grade-directed error
are taken on the same submitted row. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedTrialPivotUnits
open Finset Lattice RG Wilson Source Labels PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus XSpace.Structure1 Maxwell Maxwell.Wick
open WilsonOriginalPublicPivotRoster (Slot weight coord salaryOf)
open WilsonOriginalPublicFigureWick (project)
open WilsonOriginalPublicPivotWeights (Paid)
open WilsonPositionProgramReportedField (entire)
open scoped Classical BigOperators

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
local notation "a" => R.family.S.a
local notation "F" d:max => R.family.labels.level d

def row (d K N p:ℕ)(t:ℂ)(v:R.family.label d): (F d).Coeff:=
  entire R d K (N,p) ((t * (((a K:ℂ)^d)⁻¹)) • v)

def ceiling (d m:ℕ)(t:ℂ)(v:R.family.label d):ℝ:=
  (a m^d)⁻¹*‖t‖*(salaryOf W (F d)*(2:ℝ)^
    (Finset.univ.sup fun i:(F d).Index=>((F d).grades i).2))*(F d).coeffSize v

theorem income (d m K N p:ℕ)(live:K≤N)(t:ℂ)(v:R.family.label d):
    let δ:=a K/a m
    let vK:=row R d K N p t v
    δ^d*(∑b:Slot G d,‖coord (project W (F d) vK) b‖) ≤ ceiling R W d m t v:=by
  let vK:=row R d K N p t v
  have primary:=WilsonOriginalPublicPivotRoster.measured W (F d) vK
  have group:=WilsonPositionProgramReportedField.purchased R d K (N,p) live
    ((t*(((a K:ℂ)^d)⁻¹)) • v)
  change (F d).coeffSize vK ≤ _ at group
  rw [RG12.mass,Extra.Histories.Size.smul,norm_mul,norm_inv,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg (R.family.S.a_pos K).le] at group
  have sp:(0:ℝ)≤WilsonOriginalPublicPivotRoster.salaryOf W (F d):=by
    unfold WilsonOriginalPublicPivotRoster.salaryOf
    exact Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have positive:0≤(a K/a m)^d:=pow_nonneg (div_nonneg (R.family.S.a_pos K).le (R.family.S.a_pos m).le) _
  refine (mul_le_mul_of_nonneg_left (primary.trans (mul_le_mul_of_nonneg_left group sp)) positive).trans_eq ?_
  unfold ceiling
  rw [div_pow]
  field_simp [(R.family.S.a_pos m).ne',(R.family.S.a_pos K).ne']

/-- A priced transmitting row retains its assigned destination grade even when
some of its input coordinates have lower weight. -/
theorem transmitted (d m K N p:ℕ)(live:K≤N)(t:ℂ)(v:R.family.label d)
    (U:Matrix Unit (Slot G d) ℂ){B:ℝ}(nn:0≤B)
    (paid:Paid (a K/a m) (fun _:Unit=>d) weight U B):
    let δ:=a K/a m
    let vK:=row R d K N p t v
    ‖∑b:Slot G d,U () b*((δ:ℂ)^weight b*coord (project W (F d) vK) b)‖ ≤
      B*ceiling R W d m t v:=by
  have point:=WilsonOriginalPublicPivotWeights.applied
    (div_nonneg (R.family.S.a_pos K).le (R.family.S.a_pos m).le) paid
    (coord (project W (F d) (row R d K N p t v))) ()
  exact point.trans ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left (income R W d m K N p live t v) nn))

end YM.Integration.WilsonAddressedTrialPivotUnits
end
