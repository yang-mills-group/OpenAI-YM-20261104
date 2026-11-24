import YM.Integration.WilsonMeasuredPublicEntranceRegisteredColor

/-! Absolute colour on one named physical field map. A finite menu of the original
recorded tests determines all its free moments. With the signed action fixed, the
remaining freedom is a single colour isometry and its Cartan sign. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceActionGram
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open WilsonMeasuredPublicEntranceFiniteFreeTests WilsonMeasuredPublicEntranceCommonColor
open WilsonMeasuredPublicEntranceMarkedQuadratics
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

open PertExtension.Rigidity.Positive
open WilsonPhysicalPositionReflectedReturn (sites clear)
theorem physical {d:ℕ}(A:Module.End ℂ (D d))
    (all:∀{n:ℕ}(v:Fin n→HFields G d){x:Points n},x∈conf n→
      Wick.moment G x (fun i=>((carried C A) (v i)).val)=Wick.moment G x (fun i=>(v i).val))
    {n:ℕ}(v:Fin n→D d){x:Points n}(hx:x∈conf n):
    WickGoal (C:=C) (d:=fun _=>d) (fun i=>A (v i)) x=WickGoal (C:=C) (d:=fun _=>d) v x:=by
  let U:=fields C.labels d
  let T:=carried C A
  have lequiv(i:Fin n):U.symm (T (U (v i)))=A (v i):=by
    change U.symm (U (A (U.symm (U (v i)))))=_
    rw [U.symm_apply_apply,U.symm_apply_apply]
  have next:=WilsonPositionPrescribedScreen.zero (C:=C) d n (fun i=>T (U (v i))) x
  have old:=WilsonPositionPrescribedScreen.zero (C:=C) d n (fun i=>U (v i)) x
  change WickGoal (C:=C) (d:=fun _=>d) (fun i=>U.symm (T (U (v i)))) x=_ at next
  simp only [lequiv] at next
  change WickGoal (C:=C) (d:=fun _=>d) (fun i=>U.symm (U (v i))) x=_ at old
  simp only [U.symm_apply_apply] at old
  exact next.trans ((all (fun i=>U (v i)) hx).trans old.symm)

theorem original {d:ℕ}(A:Module.End ℂ (D d))(native:WilsonPhysicalPositionAdmissible.Native C A)
    (all:∀{n:ℕ}(v:Fin n→HFields G d){x:Points n},x∈conf n→
      Wick.moment G x (fun i=>((carried C A) (v i)).val)=Wick.moment G x (fun i=>(v i).val))
    (v:D d):gram C.labels (hierarchy C.labels) 0 (A v) (A v)=gram C.labels (hierarchy C.labels) 0 v v:=by
  let M:=Bel C.book
  let adj:=M.adj (spin_free C.labels) d 0
  have comm:A (adj v)=adj (A v):=by
    change A (WilsonPhysicalPositionAdmissible.turns C d (Signed.mirror 0)
      (WilsonPhysicalPositionAdmissible.real C d v))=_
    rw [native.orientation,native.conjugate]
    rfl
  let given:Fin 2→D d:=![v,adj v]
  have paid:=physical A all given clear
  have read (w:D d):(gramC C.labels (hierarchy C.labels) 0 w w)=
      WickGoal (C:=C) (d:=fun _:Fin 2=>d) ![w,adj w] sites:=by
    rw [gramC_apply]
    change M.useAt M sites _=M.useAt M sites (fun i:Fin 2=>(⟨d,(![w,adj w]:Fin 2→D d) i⟩:M.Tag))
    apply congrArg (M.useAt M sites)
    funext i
    fin_cases i <;> rfl
  change (gramC C.labels (hierarchy C.labels) 0 (A v) (A v)).re=(gramC C.labels (hierarchy C.labels) 0 v v).re
  rw [read,read]
  apply congrArg Complex.re
  have eq:(fun i=>A (given i))=(![A v,adj (A v)]:Fin 2→D d):=by
    funext i
    fin_cases i
    · rfl
    exact comm
  rwa [←eq]
end YM.Integration.WilsonMeasuredPublicEntranceActionGram
