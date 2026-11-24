import YM.RG.History

/-! Six untouched fields of the native physical representation under an activity update. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedRepFields
open Lattice RG
variable {G : Gauge} {n : Side}

structure Fields (kept current : Rep G n) : Prop where
  path : kept.path=current.path
  clip : kept.clip=current.clip
  coupling : kept.beta=current.beta
  vacuum : kept.v=current.v
  forced : kept.activities.forced=current.activities.forced
  charges : kept.activities.K=current.activities.K

theorem replace (base : Rep G n) (A : Activities G n)
    (forced : A.forced=base.activities.forced) (charges : A.K=base.activities.K) :
    Fields ({base with activities := A} : Rep G n) base :=
  ⟨rfl,rfl,rfl,rfl,forced,charges⟩

end YM.Integration.OriginalMarkedRepFields
