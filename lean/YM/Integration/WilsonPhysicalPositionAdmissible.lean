import YM.Integration.WilsonPhysicalPositionBornTransition
import YM.RG12.Roof.Echelons

/-! A map on the measured Maxwell quotient has an allowed position chart
when it respects the physical unit, lower fields, reality and signed spatial
symmetries. The coordinates are taken only after the whole map. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionAdmissible
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Topology Classical BigOperators
variable {G:Gauge}(C:Family G)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field
abbrev unit (d:ℕ):D d:=(Bel C.book).unit d
abbrev real (d:ℕ):D d→D d:=(Bel C.book).conj (spin_free C.labels) d
abbrev turns (d:ℕ)(s:Signed):D d→D d:=(Bel C.book).mirror (spin_free C.labels) d s

structure Native {d:ℕ}(T:D d→ₗ[ℂ]D d):Prop where
  neutral:T (unit C d)=unit C d
  lower:∀{j:ℕ}(h:j≤d)(v:D j),T ((scheme C.labels).rise h v)∈LinearMap.range ((scheme C.labels).rise h)
  conjugate:∀v,T (real C d v)=real C d (T v)
  orientation:∀s v,T (turns C d s v)=turns C d s (T v)

private theorem one {d:ℕ}:fields C.labels d (unit C d)=leaf G d:=Subtype.ext (unit_address _ _)
private theorem star {d:ℕ}(v:D d):fields C.labels d (real C d v)=reel d (fields C.labels d v):=
  Subtype.ext (address_star ..)
private theorem face {d:ℕ}(s:Signed)(v:D d):fields C.labels d (turns C d s v)=ori s.ortho d (fields C.labels d v):=
  Subtype.ext (address_motion ..)

theorem coordinates {d:ℕ}{T:D d→ₗ[ℂ]D d}(h:Native C T):
    ∃a:MoveSpace G d,WilsonPhysicalPositionBornTransition.present (C:=C)
      (WilsonPhysicalPositionDiscreteBranches.field a)=T:=by
  let U:=fields C.labels d
  let X:FieldEnd G d:=U.toLinearMap ∘ₗ T ∘ₗ U.symm.toLinearMap
  have ev (p:Sec G d):X p=U (T (U.symm p)):=rfl
  have onU:X (leaf G d)=leaf G d:=by
    rw [ev,←one C,show U.symm ((fields C.labels d) (unit C d))=unit C d from U.symm_apply_apply _,h.neutral]
  have onL {j:ℕ}(hj:j≤d)(p:Sec G d)(hp:p.val∈shellSector G j):(X p).val∈shellSector G j:=by
    let z:Sec G j:=⟨p.val,hp⟩
    let v:=(fields C.labels j).symm z
    have hz:(scheme C.labels).rise hj v=U.symm p:=by
      apply address_inj C.labels d
      rw [address_rise,address_eval,address_eval]
      change ((fields C.labels j) ((fields C.labels j).symm z)).val=(U (U.symm p)).val
      rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
    obtain ⟨w,hw⟩:=h.lower hj v
    rw [ev,←hz,←hw]
    change address C.labels d ((scheme C.labels).rise hj w)∈shellSector G j
    rw [address_rise];exact address_in C.labels j w
  have onR (p:Sec G d):X (reel d p)=reel d (X p):=by
    have eq:U (real C d (U.symm p))=reel d p:=(star C _).trans (congrArg (reel d) (U.apply_symm_apply p))
    rw [ev,←eq,U.symm_apply_apply,h.conjugate,ev]
    exact star C _
  have onS (s:Signed)(p:Sec G d):X (ori s.ortho d p)=ori s.ortho d (X p):=by
    have eq:U (turns C d s (U.symm p))=ori s.ortho d p:=(face C s _).trans (congrArg (ori s.ortho d) (U.apply_symm_apply p))
    rw [ev,←eq,U.symm_apply_apply,h.orientation,ev]
    exact face C _ _
  have changeX:X-LinearMap.id∈Change G d:=by
    apply (may_change _).mpr
    refine ⟨?_,?_,?_,?_⟩
    · change X (leaf G d)-leaf G d=0;rw [onU,sub_self]
    · intro j hj p hp
      exact Submodule.sub_mem _ (onL hj p hp) hp
    · intro p
      change X (reel d p)-reel d p=reel d (X p-p)
      rw [onR,map_sub]
    · intro s p
      change X (ori s.ortho d p)-ori s.ortho d p=ori s.ortho d (X p-p)
      rw [onS,map_sub]
  let m:Change G d:=⟨X-LinearMap.id,changeX⟩
  refine ⟨guide G d m,?_⟩
  have exactX (v:Sec G d):WilsonPhysicalPositionDiscreteBranches.field (guide G d m) v=X v:=by
    unfold WilsonPhysicalPositionDiscreteBranches.field
    rw [LinearEquiv.symm_apply_apply,stood]
    change v+(X v-v)=X v
    abel
  apply LinearMap.ext;intro v
  change U.symm (WilsonPhysicalPositionDiscreteBranches.field (guide G d m) (U v))=T v
  rw [exactX,ev,U.symm_apply_apply,U.symm_apply_apply]

end YM.Integration.WilsonPhysicalPositionAdmissible
end
