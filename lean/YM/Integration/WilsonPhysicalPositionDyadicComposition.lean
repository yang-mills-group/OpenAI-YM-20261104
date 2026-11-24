import YM.Integration.WilsonPhysicalPositionOnePanel

/-! Exact composition of two measured changes of radius. The engineering
conjugation is necessary when a field has lower-weight components. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionDyadicComposition
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace
open WilsonPhysicalPositionUniformBranches (change)
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{S:Table C.book}
variable (J:ℝ→tower S)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field

theorem composed {d:ℕ}(r u t:ℝ)(hu:0<u)(ht:0<t)(v:D d):
    Frame.cocycle d J r (u*t) (mul_pos hu ht) v=
      (Pert.Scale.gearIso C.labels d t ht).symm
        (Frame.cocycle d J r u hu (Pert.Scale.gear C.labels d t (Frame.cocycle d J (u*r) t ht v))):=by
  apply (Pert.Scale.gearIso C.labels d t ht).injective
  rw [LinearEquiv.apply_symm_apply]
  apply (Pert.Scale.gearIso C.labels d u hu).injective
  apply (J r d).injective
  change J r d (Pert.Scale.gear C.labels d u (Pert.Scale.gear C.labels d t _))=
    J r d (Pert.Scale.gear C.labels d u (Frame.cocycle d J r u hu _))
  rw [Pert.Scale.gear_chain,Frame.cocycle_value,Frame.cocycle_value,Frame.cocycle_value]
  rw [mul_assoc,mul_left_comm]

private theorem tariff {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E]
    (A B L U:E→L[ℂ]E)(inv:U.comp L=ContinuousLinearMap.id ℂ E):
    ‖U.comp (A.comp (L.comp B))-ContinuousLinearMap.id ℂ E‖≤
      ‖U‖*(‖A-ContinuousLinearMap.id ℂ E‖*(‖L‖*‖B‖))+‖B-ContinuousLinearMap.id ℂ E‖:=by
  let I:=ContinuousLinearMap.id ℂ E
  have split:U.comp (A.comp (L.comp B))-I=U.comp ((A-I).comp (L.comp B))+(B-I):=by
    ext1 x
    have cancel:=congrArg (fun K:E→L[ℂ]E=>K (B x)) inv
    change U (L (B x))=B x at cancel
    change U (A (L (B x)))-x=U (A (L (B x))-L (B x))+(B x-x)
    rw [map_sub,cancel]
    abel
  rw [split]
  refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
    (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))

theorem original (d:ℕ)(t:ℝ)(ht:0<t):
    ∃H:ℝ,0≤H ∧ ∀(r u:ℝ)(hu:0<u),
    ‖change J d r (u*t) (mul_pos hu ht)-ContinuousLinearMap.id ℂ (D d)‖≤
    H*‖change J d r u hu-ContinuousLinearMap.id ℂ (D d)‖*‖change J d (u*r) t ht‖+
       ‖change J d (u*r) t ht-ContinuousLinearMap.id ℂ (D d)‖:=by
  let L:=(Pert.Scale.gearIso C.labels d t ht).toLinearMap.toContinuousLinearMap
  let U:=(Pert.Scale.gearIso C.labels d t ht).symm.toLinearMap.toContinuousLinearMap
  have inv:U.comp L=ContinuousLinearMap.id ℂ (D d):=by
    ext1 x
    exact (Pert.Scale.gearIso C.labels d t ht).symm_apply_apply x
  refine ⟨‖U‖*‖L‖,mul_nonneg U.opNorm_nonneg L.opNorm_nonneg,?_⟩
  intro r u hu
  let A:=change J d r u hu
  let B:=change J d (u*r) t ht
  have eq:change J d r (u*t) (mul_pos hu ht)=U.comp (A.comp (L.comp B)):=by
    ext1 x
    exact composed J r u t hu ht x
  rw [eq]
  exact (tariff A B L U inv).trans_eq (by ring)

end YM.Integration.WilsonPhysicalPositionDyadicComposition
end
