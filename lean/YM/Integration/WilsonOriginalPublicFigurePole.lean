import YM.Integration.WilsonOriginalPublicFigureIncome
import YM.Integration.WilsonPositionProgramTrialThermalGrades

/-! The common pole is cleared before the normalization. Evaluating the filed
group function at the physical coupling restores every original input and its unit. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicFigurePole
open Wilson RG Labels Lattice Finset PowerSeries PhysicalNext.Repeat.Legato XSpace
open RegulatorIR RegulatorIR.FVAAlt2 PertExtension PertExtension.Orb Precision
open WilsonThermometerPositionTunedSlope (Columns paid finite)
open WilsonPositionProgramTrialThermalGrades (frozen restored)
open scoped Classical BigOperators PowerSeries
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I → ℕ)
local notation "E" i:max => R.family.labels.level (d i)
def roof:=∑i,WilsonOriginalPublicFigureIncome.height R (d i)

omit [LinearOrder I] in
theorem enough (a:Columns R d):Kick.depthF univ d a ≤ roof R d:=
  sum_le_sum fun i _=>le_sup (f:=fun b:(E i).Index=>((E i).grades b).2) (mem_univ (a i))

variable (v:(i:I) → (R.family.labels.level (d i)).Coeff)(z:I → Cover)
def opening (v:(i:I) → (R.family.labels.level (d i)).Coeff) (z:I → Cover) (g:ℝ){n:Side}(U:Config G n):ℂ:=
  ∑a:Columns R d, (g:ℂ)^(roof R d-Kick.depthF univ d a)*(∏i:I,v i (a i))*
    ((Sound.Figure.prop R (fun _:Unit=>z) d a ()).Vt n U:ℝ)

theorem field (g:ℝ)(nonzero:g≠0){n:Side}(U:Config G n):
    opening R d v z g U=(g:ℂ)^roof R d*WilsonOriginalPublicTrialFigure.measured R d g v z U:=by
  rw [opening,WilsonOriginalPublicTrialFigure.opened,mul_sum]
  apply sum_congr rfl
  intro a _
  rw [←restored R d nonzero v a,←mul_assoc ((g:ℂ)^roof R d)]
  congr 1
  rw [show (g:ℂ)^roof R d=(g:ℂ)^(roof R d-Kick.depthF univ d a)*(g:ℂ)^Kick.depthF univ d a from
    ((pow_add ..).symm.trans (congrArg ((g:ℂ)^·) (Nat.sub_add_cancel (enough R d a)))).symm]
  ring

variable (P:Period)(T:P.Tree)
def material (v:(i:I) → (R.family.labels.level (d i)).Coeff) (z:I → Cover) (P:Period) (T:P.Tree): Bare.Series T G:=
  ∑a:Columns R d, Bare.scalar T (PowerSeries.X^(roof R d-Kick.depthF univ d a)*
    PowerSeries.C (∏i:I,v i (a i))) * Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘
      (WilsonPositionProgramCopyTop.planted R P d z a ∘ T.links))

theorem filed: Bare.normalized T G (material R d v z P T)=
    PowerSeries.X^(roof R d)*paid R d (frozen R d v) (finite R d P z T):=by
  rw [material,map_sum,paid,mul_sum]
  apply sum_congr rfl
  intro a _
  have head:WilsonThermometerPositionTunedSlope.price R d (frozen R d v) a=
      PowerSeries.C (∏i:I,v i (a i)):=(map_prod PowerSeries.C _ univ).symm
  rw [Bare.normalized_scalar,head]
  change (_*PowerSeries.C _)*WilsonPositionProgramCopyTop.normalized R P d z a T=_
  have rank:WilsonPositionProgramCopyTop.normalized R P d z a T=
      PowerSeries.X^(Kick.depthF univ d a)*finite R d P z T a:=by
    ext k
    rw [PowerSeries.coeff_X_pow_mul']
    split
    · rename_i inside
      simp only [finite,coeff_mk,Nat.sub_add_cancel inside]
    · rename_i tooLow
      exact WilsonPositionProgramInversionRank.original R P d z a T k (Nat.lt_of_not_ge tooLow)
  rw [rank,show (PowerSeries.X:PowerSeries ℂ)^roof R d=PowerSeries.X^(roof R d-Kick.depthF univ d a)*
      PowerSeries.X^(Kick.depthF univ d a) from ((pow_add ..).symm.trans
        (congrArg ((PowerSeries.X:PowerSeries ℂ)^·) (Nat.sub_add_cancel (enough R d a)))).symm]
  ring

theorem original (q:ℕ):
    coeff (q+roof R d) (Bare.normalized T G (material R d v z P T))=
      ∑a:Columns R d,(∏i:I,v i (a i))*
        coeff (q+Kick.depthF univ d a) (WilsonPositionProgramCopyTop.normalized R P d z a T):=by
  rw [filed,PowerSeries.coeff_X_pow_mul',if_pos (Nat.le_add_left _ _),Nat.add_sub_cancel]
  exact WilsonPositionProgramTrialThermalGrades.coefficient R d v z P T q

end YM.Integration.WilsonOriginalPublicFigurePole
end
