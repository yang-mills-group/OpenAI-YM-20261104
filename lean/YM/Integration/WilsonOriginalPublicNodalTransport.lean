import YM.Integration.WilsonOriginalPublicFigurePole
import YM.Integration.WilsonReflectedPlacedArm
import YM.Integration.ActualWilsonAbsoluteTransport

/-! The fitted K trial and each of its literal public group functions are carried
through the same nonbare Wilson history before any numerical table is compared. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonOriginalPublicNodalTransport
open Finset Lattice Wilson RG Source Labels MeasureTheory
open RegulatorIR.FVAAlt2 Pert.Asymptotics Extra.Histories PhysicalNext PhysicalNext.Repeat.Legato
open WilsonOriginalMicroscopicGuardedPageSchool WilsonOriginalMicroscopicGuardedTrial
open WilsonOriginalPublicTrialInput WilsonOriginalPublicTrialFigure
open WilsonThermometerPositionTunedSlope (Columns)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per K u:ℕ}
local notation "X" n:max => Config G (R.family.side n per)
local notation "T" => actualTransport R.family (N:=N) (p:=per)

private theorem zero (live:K≤N)(stop:u≤K)(U:X u):T (0:X K→ℂ) stop U=0:=by
  have hf:=ActualWilsonAbsoluteTransport.weighted R.family R.makes live
    (Envelope.compactC (continuous_zero:Continuous (0:X K→ℂ)))
  have h:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes live hf hf stop) U
  change T (fun V:X K=>(0:X K→ℂ) V-(0:X K→ℂ) V) stop U=_ at h
  have eq:(fun V:X K=>(0:X K→ℂ) V-(0:X K→ℂ) V)=(0:X K→ℂ):=by funext V;exact sub_self _
  rw [eq,sub_self] at h
  exact h

private theorem add (live:K≤N)(stop:u≤K)(U:X u)(F H:X K→ℂ)
    (hF:Continuous F)(hH:Continuous H):
    T (F+H) stop U=T F stop U+T H stop U:=by
  have hf:=ActualWilsonAbsoluteTransport.weighted R.family R.makes live
    (Envelope.compactC (hF.add hH))
  have hh:=ActualWilsonAbsoluteTransport.weighted R.family R.makes live (Envelope.compactC hH)
  have h:=congrFun (ActualWilsonAbsoluteTransport.sub R.family R.makes live hf hh stop) U
  change T (F+H-H) stop U=T (F+H) stop U-T H stop U at h
  rw [add_sub_cancel_right] at h
  linear_combination -h

theorem roster {ι:Type}(s:Finset ι)(live:K≤N)(stop:u≤K)(U:X u)
    (c:ι→ℂ)(F:ι→X K→ℂ)(continuous:∀i,Continuous (F i)):
    T (∑i∈s,c i • F i) stop U=∑i∈s,c i*T (F i) stop U:=by
  induction s using Finset.induction_on with
  | empty=>simpa using zero R live stop U
  | @insert i s hi ih=>
    rw [sum_insert hi,sum_insert hi,add R live stop U]
    · rw [ih,WilsonReflectedPlacedArm.linear R live stop (F i) (Envelope.compactC (continuous i)) (c i) U]
    · exact continuous_const.smul (continuous i)
    · change Continuous (fun U=>(∑j∈s,c j • F j) U)
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
      exact continuous_finsetSum _ fun j _=>continuous_const.mul (continuous j)

variable {I:Type}[Fintype I][LinearOrder I](d:I→ℕ)
def group (z:I→ Cover)(a:Columns R d)(n:Side)(U:Config G n):ℂ:=
  ((Sound.Figure.prop R (fun _:Unit=>z) d a ()).Vt n U:ℝ)

theorem continuous (z:I→ Cover)(a:Columns R d)(n:Side):
    Continuous (group R d z a n):=
  Complex.continuous_ofReal.comp ((Sound.Figure.prop R (fun _:Unit=>z) d a ()).payment n)

theorem filed (live:K≤N)(stop:u≤K)(U:X u)(g:ℝ)
    (v:∀i,(R.family.labels.level (d i)).Coeff)(z:I→ Cover):
    T (measured R d g v z) stop U=
      ∑a:Columns R d,weight R d g v a*T (group R d z a _) stop U:=by
  have field:measured R d g v z (n:=R.family.side K per)=
      ∑a:Columns R d,weight R d g v a • group R d z a _:=by
    funext V
    simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,group] using
      WilsonOriginalPublicTrialFigure.opened R d g v z _ V
  rw [field]
  exact roster R univ live stop U _ _ fun a=>continuous R d z a _

omit d in
/-- The original chosen coordinates in all three arms are fixed before their
positions. Each surviving subset may repeat, omit or reorder those arms. -/
theorem original (grades j:Fin 3→ℕ)(target:ℕ)(η:ℝ)(M:Fin 3→ℝ)
    (Y:∀a:Fin 3,ℕ×ℕ→R.family.label (grades a))
    (before:∀a,j a≤K)(registered:Indexed R grades j target η M Y)
    (live:K<N)(stop:u≤K)(child:I→Fin 3)
    (o:Fin 3→Site (R.family.side K per))(z:I→ Cover)
    (lift:∀i,wrap (R.family.side K per) (z i)=o (child i))(U:X u):
    T (fun V=>∏i,raw R grades N per K o
      (fitted R grades j K target η M Y before registered N per) (child i) V) stop U=
    ∑a:Columns R (grades ∘ child),weight R (grades ∘ child) (regulatorRun R.family N per K)
      (fun i=>vector R grades j K target η M Y before registered N per (child i)) a*
       T (group R (grades ∘ child) z a _) stop U:=by
  let v:=fun i=>vector R grades j K target η M Y before registered N per (child i)
  have source:(fun V:X K=>∏i,raw R grades N per K o
      (fitted R grades j K target η M Y before registered N per) (child i) V)=
      measured R (grades ∘ child) (regulatorRun R.family N per K) v z:=by
    funext V
    exact (WilsonOriginalPublicTrialFigure.original R grades j K target η M Y before registered
      N per live child o z lift V).trans
        (WilsonOriginalPublicTrialFigure.opened R _ _ v z _ V).symm
  rw [source]
  exact filed R (grades ∘ child) live.le stop U _ v z

end YM.Integration.WilsonOriginalPublicNodalTransport
end
