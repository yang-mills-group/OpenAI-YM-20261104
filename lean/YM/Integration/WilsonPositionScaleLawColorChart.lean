import YM.Integration.WilsonPhysicalPositionDiscreteBranches
import YM.Integration.WilsonPositionPrescribedFormalResidual

/-! A single admissible color convention passes through every input of the numerical
position equations. The chosen position tests are kept verbatim. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawColorChart
open Function Filter Set Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionDiscreteBranches (field shift)
open WilsonPhysicalPositionChangeCancellation (cost cross)
open scoped Topology Classical
variable {G:Gauge}{d:ℕ}
local notation "M" => MoveSpace G d

def move (x:M):FieldEnd G d:=((guide G d).symm x).val

def right (a:M):M→ₗ[ℝ]M:=LinearMap.id+(cost G d).flip a

def conjugate (a b:M):M→ₗ[ℝ]M:=(shift b).comp (right a)

theorem leftLeg (a x:M)(p:Sec G d):move (shift a x) p=field a (move x p):=by
  change ((guide G d).symm (x+guide G d (cross _ _))).val p=_
  rw [map_add,LinearEquiv.symm_apply_apply]
  rfl

theorem rightLeg (a x:M)(p:Sec G d):move (right a x) p=move x (field a p):=by
  change ((guide G d).symm (x+guide G d (cross _ _))).val p=_
  rw [map_add,LinearEquiv.symm_apply_apply]
  change move x p+move x (move a p)=move x (p+move a p)
  rw [map_add]

theorem leg (a b x:M)(p:Sec G d):move (conjugate a b x) p=field b (move x (field a p)):=by
  change move (shift b (right a x)) p=_
  rw [leftLeg,rightLeg]

theorem strip (a b:M)(inv:field a ∘ₗ field b=1)(x:M):
    field a ∘ₗ field (conjugate a b x)=field x ∘ₗ field a:=by
  ext1 p
  have h:=DFunLike.congr_fun inv (move x (field a p))
  change field a (field b (move x (field a p)))=move x (field a p) at h
  change field a (p+move (conjugate a b x) p)=field a p+move x (field a p)
  rw [map_add,leg,h]

theorem allArms (a b:M)(inv:field a ∘ₗ field b=1)(x:M)
    {E:Type}[AddCommMonoid E][Module ℂ E](P:Correl G d E):
    recruit (field x ∘ₗ field a) P = recruit (field (conjugate a b x)) (recruit (field a) P):=by
  rw [recruits_comp,strip a b inv]

theorem small {I:Type*}{u:Filter I}(a b:M){x:I→M}(hx:Tendsto x u (𝓝 0)):
    Tendsto (fun i=>conjugate a b (x i)) u (𝓝 0):=by
  simpa only [map_zero] using! (((conjugate a b).toContinuousLinearMap.continuous.tendsto 0).comp hx)

end YM.Integration.WilsonPositionScaleLawColorChart
end
