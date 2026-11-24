import YM.Integration.WilsonPositionPrescribedScreen

/-! A finite signed target is tested in its own public frame at each of its genuine home radii. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionTargetRows
open Function Filter Set Finset Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{d n:ℕ}{I:Type}

abbrev Array (G:Gauge)(d n:ℕ):=(Fin n→Pin G d)→ℂ

def rows (M:MultilinearMap ℂ (fun _:Fin n=> Sec G d) ℂ):Array G d n:=fun b=>
  M (fun j=>Module.finBasis ℝ (Sec G d) (b j))

def velocity (v:Sec G d):MoveSpace G d→L[ℝ]RSpace G d:=
  LinearMap.toContinuousLinearMap { toFun c:=tableD G d (((guide G d).symm c).val v), map_add' :=by intro a b;rw [map_add];exact map_add (tableD G d) _ _, map_smul' :=by intro a b;rw [map_smul];exact map_smul (tableD G d) _ _ }

theorem leg (v:Sec G d)(j:Pin G d):
    ContDiff ℝ ω (fun x:MoveSpace G d=>tableD G d (Fray.box x v) j):=by
  simp_rw [Fray.box,stood,map_add,Pi.add_apply]
  exact contDiff_const.add ((contDiff_apply ℝ ℝ j).comp (velocity v).contDiff)

def meter (home:Fin n→I)(v:Fin n→Sec G d)(x:I→MoveSpace G d):Array G d n→L[ℝ]ℂ:=
  ∑ b:Fin n→Pin G d,(∏j,tableD G d (Fray.box (x (home j)) (v j)) (b j)) •
    (ContinuousLinearMap.proj (R:=ℝ) b)

theorem smooth [Fintype I] (home:Fin n→I)(v:Fin n→Sec G d):ContDiff ℝ ω (meter home v):=by
  unfold meter
  apply ContDiff.sum
  intro b _
  apply ContDiff.smul (f:=fun x:I→MoveSpace G d=>∏ j,tableD G d (Fray.box (x (home j)) (v j)) (b j)) (g:=fun _=>ContinuousLinearMap.proj (R:=ℝ) b) _ contDiff_const
  apply contDiff_prod
  intro j _
  exact (leg (v j) (b j)).comp (contDiff_apply ℝ (MoveSpace G d) (home j))

theorem counted (home:Fin n→I)(v:Fin n→Sec G d)(M:MultilinearMap ℂ (fun _:Fin n=> Sec G d) ℂ)
    (s:I→Change G d):
    meter home v (fun i=>guide G d (s i)) (rows M)=M (fun j=>stand (s (home j)) (v j)):=by
  simpa [meter,rows,Fray.box,_root_.sum_apply] using
    (medium (fun j=>stand (s (home j)) (v j)) (M.restrictScalars ℝ)).symm

theorem zero (home:Fin n→I)(v:Fin n→Sec G d)(M:MultilinearMap ℂ (fun _:Fin n=> Sec G d) ℂ):
    meter home v 0 (rows M)=M v:=by
  simpa [Pi.zero_def,stand0] using counted home v M (fun _=>0)

end YM.Integration.WilsonPhysicalPositionTargetRows
