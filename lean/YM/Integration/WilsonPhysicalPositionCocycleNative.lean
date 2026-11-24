import YM.Integration.WilsonPhysicalPositionAdmissible
import YM.Integration.WilsonPhysicalPositionPhysicalBranches

/-! The bounded-ratio *physical* frame transition has an allowed chart on
the same elected Wilson hierarchy. All smaller filtration levels are used
at the same two radii before passing to an operator limit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionCocycleNative
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionAdmissible
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
variable (F:Final C f S)(J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

structure Income (d:ℕ)(s:ℝ):Prop where
  neutral:J s d (unit C d)=S.unit d
  real:Spin.realH F.room.kernel.spin (spin_free C.labels) (J s d)
  lower:∀{j:ℕ}(h:j≤d)(v:D j),J s d ((scheme C.labels).rise h v)=F.sector.derivatives.rise h (J s j v)

theorem purchased (h:Leading F J)(d:ℕ):∀ᶠ r in trail,Income F J d r:=by
  have lower:∀ᶠ r in trail,∀j:Fin (d+1),∀v,J r d ((scheme C.labels).rise (Nat.le_of_lt_succ j.isLt) v)=
      F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt) (J r j v):=by
    apply eventually_all.mpr
    intro j
    exact h.raised _
  filter_upwards [h.unit d,h.equivariant d,lower] with r hu he hl
  exact ⟨hu,he,fun {j} hj=>hl ⟨j,Nat.lt_succ_of_le hj⟩⟩

private theorem mirror {d:ℕ}(t:ℝ)(s:Signed)(v:D d):Pert.Scale.gear C.labels d t (turns C d s v)=
    turns C d s (Pert.Scale.gear C.labels d t v):=by
  change Pert.Scale.gear C.labels d t (Pert.Rigid.wear C.labels d s v)=
    Pert.Rigid.wear C.labels d s (Pert.Scale.gear C.labels d t v)
  simp_rw [Pert.Rigid.wear_ride]
  exact (Pert.Scale.gear_spin ..).symm

private theorem expose {d:ℕ}{r t:ℝ}(ht:0<t)(v:D d):Frame.cocycle d J r t ht v=
    Pert.Scale.gear C.labels d t⁻¹ ((J r d).symm (J (t*r) d v)):=by
  let k:=Pert.Scale.gearIso C.labels d t ht
  let w:=(J r d).symm (J (t*r) d v)
  change k.symm w=Pert.Scale.gear C.labels d t⁻¹ w
  calc
    k.symm w=Pert.Scale.gear C.labels d t⁻¹ (Pert.Scale.gear C.labels d t (k.symm w)) :=
      (Pert.Scale.gear_inverse C.labels ht.ne' _).symm
    _=Pert.Scale.gear C.labels d t⁻¹ w:=congrArg _ (k.apply_symm_apply w)

theorem original {d:ℕ}{r t:ℝ}(ht:0<t)(i:Income F J d r)(k:Income F J d (t*r)):
    Native C (Frame.cocycle d J r t ht).toLinearMap:=by
  let A:=(J (t*r) d).trans (J r d).symm
  have slot(v:D d):Frame.cocycle d J r t ht v=Pert.Scale.gear C.labels d t⁻¹ (A v):=expose J ht v
  have onStar (v:D d):A (real C d v)=real C d (A v):=by
    apply (J r d).injective
    change J r d ((J r d).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (k.real.2 v).trans ((congrArg (S.conj F.room.kernel.spin d) ((J r d).apply_symm_apply _).symm).trans (i.real.2 (A v)).symm)
  have onFace (s:Signed)(v:D d):A (turns C d s v)=turns C d s (A v):=by
    apply (J r d).injective
    change J r d ((J r d).symm _) = _
    rw [LinearEquiv.apply_symm_apply]
    exact (k.real.1 s v).trans ((congrArg (S.mirror F.room.kernel.spin d s) ((J r d).apply_symm_apply _).symm).trans (i.real.1 s (A v)).symm)
  constructor
  · change Frame.cocycle d J r t ht _=_
    rw [slot]
    change Pert.Scale.gear C.labels d t⁻¹ ((J r d).symm (J (t*r) d (unit C d)))=_
    rw [k.neutral,←i.neutral,LinearEquiv.symm_apply_apply]
    exact Pert.Scale.gear_unit .. 
  · intro j hj v
    let w:=(J r j).symm (J (t*r) j v)
    have U:A ((scheme C.labels).rise hj v)=(scheme C.labels).rise hj w:=by
      apply (J r d).injective
      change J r d ((J r d).symm _) = _
      rw [LinearEquiv.apply_symm_apply]
      exact (k.lower hj v).trans ((congrArg (F.sector.derivatives.rise hj) ((J r j).apply_symm_apply _).symm).trans (i.lower hj w).symm)
    refine ⟨Pert.Scale.gear C.labels j t⁻¹ w,?_⟩
    change _=Frame.cocycle d J r t ht _
    rw [slot,U,RG12.Roof.gear_rises]
  · intro v
    change Frame.cocycle d J r t ht _=real C d (Frame.cocycle d J r t ht _)
    rw [slot,slot,onStar]
    exact (Pert.Scale.gear_conj ..).symm
  · intro s v
    change Frame.cocycle d J r t ht _=turns C d s (Frame.cocycle d J r t ht _)
    rw [slot,slot,onFace]
    exact mirror _ _ _

end YM.Integration.WilsonPhysicalPositionCocycleNative
end
