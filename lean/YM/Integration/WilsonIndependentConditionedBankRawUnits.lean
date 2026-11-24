import YM.Integration.WilsonAddressedSharpTrialUnits
import YM.Integration.WilsonAddressedTrialKineticAperture

/-! Entire physical trial at its actual addressed K, before any quotient projection. -/
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRawUnits
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
variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)
local notation "a" => R.family.S.a
local notation "F" d:max => R.family.labels.level d

def home (d j f:ℕ)(η:ℝ)(t:ℂ)(salary:ℝ):ℝ:=
  4*‖t‖*(2:ℝ)^(Finset.univ.sup fun i:(F d).Index=>((F d).grades i).2)*
    orbitCost (F d)*salary*(a j/a f)^((d:ℝ)+η)

def raw (d f:ℕ)(t:ℂ)(v:R.family.label d):ℝ:=
  (a f^d)⁻¹*‖t‖*(2:ℝ)^(Finset.univ.sup fun i:(F d).Index=>((F d).grades i).2)*(F d).coeffSize v

theorem native (d f K N p:ℕ)(live:K ≤ N)(t:ℂ)(v:R.family.label d):
    (a K/a f)^d*(F d).coeffSize (row R d K N p t v) ≤ raw R d f t v:=by
  have group:=WilsonPositionProgramReportedField.purchased R d K (N,p) live ((t*(((a K:ℂ)^d)⁻¹)) • v)
  change (F d).coeffSize (row R d K N p t v) ≤ _ at group
  rw [RG12.mass,Extra.Histories.Size.smul,norm_mul,norm_inv,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg (R.family.S.a_pos K).le] at group
  have positive:0 ≤ (a K/a f)^d:=pow_nonneg (div_nonneg (R.family.S.a_pos K).le (R.family.S.a_pos f).le) _
  refine (mul_le_mul_of_nonneg_left group positive).trans_eq ?_
  unfold raw
  rw [div_pow]
  field_simp [(R.family.S.a_pos f).ne',(R.family.S.a_pos K).ne']
variable {d j f K N p target:ℕ}(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ}
  (A:(R.family.label d)≃ₗ[ℂ](R.family.label d))(Y:R.family.label d) {salary:ℝ}
  (cash:Cash (R:=R) d j f K N p target before up live η A Y salary)
  (arm:Arm R d N p f K) (same:arm.w=A.symm (fitted R d j N p Y))

include cash same in
theorem received (t:ℂ):
    raw R d f t (coords R arm)  ≤  home R d j f η t salary*(a f/a K)^η:=by
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
  have unturned:(F d).coeffSize arm.w  ≤  stretch R η j K*(2*(a j^d*salary)):=by
    rw [same]
    exact cash.2.1
  have op:0 ≤ orbitCost (F d):=zero_le_one.trans (orbitCost_one_le _)
  have measured:= (patch_cost (F d) (arm.s,arm.b) arm.w).trans (mul_le_mul_of_nonneg_left unturned op)
  change (F d).coeffSize (coords R arm)  ≤  _ at measured
  unfold raw home
  refine (mul_le_mul_of_nonneg_left measured (by positivity)).trans_eq ?_
  rw [phase,split,Real.rpow_add (div_pos aj af),Real.rpow_natCast,div_pow]
  ring

include cash same in
theorem original (t:ℂ):
    let δ:=a K/a f
    δ^d*(F d).coeffSize (row R d K N p t (coords R arm))  ≤  home R d j f η t salary*δ^(-η):=by
  intro δ
  apply (native R d f K N p live t (coords R arm)).trans
  have dp:0<δ:=div_pos (R.family.S.a_pos _) (R.family.S.a_pos _)
  have eq:(a f/a K)^η=δ^(-η):=by
    dsimp only [δ]
    rw [Real.rpow_neg dp.le,←Real.inv_rpow (div_nonneg (R.family.S.a_pos _).le (R.family.S.a_pos _).le),inv_div]
  rw [←eq]
  exact received R before up live A Y cash arm same t

end YM.Integration.WilsonIndependentConditionedBankRawUnits
end
