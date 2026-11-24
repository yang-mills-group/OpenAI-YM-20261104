import YM.Integration.WilsonOriginalPublicNodalTransport
import YM.Integration.WilsonOriginalPublicPivotReflected

/-! A signed fixed-child comparison on the same finite set of original public
group functions, before either regulator is removed. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 700000
namespace YM.Integration.WilsonOriginalPublicNodalFiling
open Finset PowerSeries Lattice Wilson RG Source Labels XSpace
open RegulatorIR.FVAAlt2 Pert.Asymptotics Extra.Histories PhysicalNext PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicGuardedPageSchool WilsonOriginalMicroscopicGuardedTrial
open WilsonOriginalPublicTrialInput WilsonOriginalPublicTrialFigure
open WilsonOriginalPublicNodalTransport (group)
open WilsonThermometerPositionTunedSlope (Columns paid finite)
open WilsonPositionProgramTrialThermalGrades (frozen)
open WilsonOriginalPublicPivotReflected (evaluated)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
variable (z:I→ Cover)(P:Period)(tree:P.Tree)

def printed (a:Columns R d)(q:ℕ)(g:ℝ):ℂ:=
  ∑k∈Iic q,(g:ℂ)^(k+Kick.depthF univ d a)*
    coeff (k+Kick.depthF univ d a) (WilsonPositionProgramCopyTop.normalized R P d z a tree)

theorem independent (v:∀i,(R.family.labels.level (d i)).Coeff)(q:ℕ){g:ℝ}(hg:g≠0):
    evaluated q g (paid R d (frozen R d v) (finite R d P z tree))=
      ∑a:Columns R d,weight R d g v a*printed R d z P tree a q g:=by
  unfold evaluated
  simp_rw [←WilsonPositionProgramTrialThermalGrades.priced R d v z P tree hg]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [printed,mul_sum,mul_assoc]

variable {N per K u:ℕ}
local notation "X" j:max => Config G (R.family.side j per)
local notation "read" => actualTransport R.family (N:=N) (p:=per)

def residual (stop:u≤K)(U:X u)(a:Columns R d)(q:ℕ)(g:ℝ):ℂ:=
  read (group R d z a _) stop U-printed R d z P tree a q g

theorem issued (live:K≤N)(stop:u≤K)(U:X u)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (q:ℕ){g:ℝ}(hg:g≠0):
    read (measured R d g v z) stop U-
      evaluated q g (paid R d (frozen R d v) (finite R d P z tree))=
    ∑a:Columns R d,weight R d g v a*residual R d z P tree (N:=N) stop U a q g:=by
  rw [WilsonOriginalPublicNodalTransport.filed R d live stop U g v z,
    independent R d z P tree v q hg,←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  exact (mul_sub ..).symm

/-- A price on each single, independently declared group function is charged
at its own rank. After refitting only the true numerical vector contributes. -/
theorem priced (live:K≤N)(stop:u≤K)(U:X u)(v:∀i,(R.family.labels.level (d i)).Coeff)
    (q:ℕ){g:ℝ}(hg:g≠0)(B:Columns R d→ℝ)
    (localPay:∀a,‖residual R d z P tree (N:=N) stop U a q g‖≤
      ‖(g:ℂ)^Kick.depthF univ d a‖*B a):
    ‖read (measured R d g v z) stop U-
      evaluated q g (paid R d (frozen R d v) (finite R d P z tree))‖≤
      ∑a:Columns R d,‖∏i,v i (a i)‖*B a:=by
  rw [issued R d z P tree live stop U v q hg]
  apply (norm_sum_le ..).trans
  apply sum_le_sum
  intro a _
  rw [norm_mul]
  calc
    _≤‖weight R d g v a‖*(‖(g:ℂ)^Kick.depthF univ d a‖*B a):=
      mul_le_mul_of_nonneg_left (localPay a) (norm_nonneg _)
    _=‖∏i,v i (a i)‖*B a:=by
      rw [←mul_assoc,←norm_mul,WilsonPositionProgramTrialThermalGrades.restored R d hg]

omit d in
theorem original (grades j:Fin 3→ℕ)(target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (grades a))
    (before:∀a,j a≤K)(registered:Indexed R grades j target η M Y)
    (live:K<N)(stop:u≤K)(U:X u)(child:I→Fin 3)
    (o:Fin 3→Site (R.family.side K per))
    (lift:∀i,wrap (R.family.side K per) (z i)=o (child i))(q:ℕ)
    (warm:regulatorRun R.family N per K≠0):
    let v:=fun i=>vector R grades j K target η M Y before registered N per (child i)
    let g:=regulatorRun R.family N per K
    read (fun V=>∏i,raw R grades N per K o
      (fitted R grades j K target η M Y before registered N per) (child i) V) stop U-
      evaluated q g (paid R (grades ∘ child) (frozen R (grades ∘ child) v)
        (finite R (grades ∘ child) P z tree))=
    ∑a:Columns R (grades ∘ child),weight R (grades ∘ child) g v a*
      residual R (grades ∘ child) z P tree (N:=N) stop U a q g:=by
  intro v g
  rw [WilsonOriginalPublicNodalTransport.original R grades j target η M Y before registered
    live stop child o z lift U,independent R (grades ∘ child) z P tree v q warm,←sum_sub_distrib]
  apply sum_congr rfl
  intro a _
  exact (mul_sub ..).symm

end YM.Integration.WilsonOriginalPublicNodalFiling
end
