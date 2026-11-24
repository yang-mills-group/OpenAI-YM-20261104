import YM.FullVolume.Cross
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Test
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Null
import YM.RG02.Flat.Kernel

/-! The original fine path agrees with its complete unmasked action on a full
field neighborhood. The event precedes every real beta and retains the empty
flag identity so that every additional layer mask can use the same event. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualRunPathNeighborhood

open Filter Lattice Wilson RG
open PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge}

/-- A full neighborhood for the original fine field, uniform over real beta. -/
theorem near_identity (R : Run G) (N p m : ℕ) :
    ∀ᶠ U : Config G (R.family.side (m + 1) p) in 𝓝 1,
      flags (R.family.path.levels.budget (m + 1)).threshold U = ∅ ∧
      ∀ β : ℝ,
        (R.family.path.rep N p (m + 1)).path.inChannels
            (R.family.path.levels.params (m + 1)).clip
            (R.family.path.levels.budget (m + 1)) β U =
          β * Precision.mainTerm (R.family.path.levels.params (m + 1)).clip
            (R.family.path.rep N p (m + 1)).path U +
          Precision.loop (R.family.path.rep N p (m + 1)).path U := by
  filter_upwards [ProjectorNext.Equivariance.offFlags
    (G := G) (n := R.family.side (m + 1) p)
    (R.family.path.levels.budget (m + 1)).threshold
    (R.family.path.levels.budget (m + 1)).threshold_pos] with U hU
  exact ⟨hU, fun β => PhysicalNext.Repeat.Pane.crystalline _ _ _ β U hU⟩

/-- Pull the same event through the native complete field chart. -/
theorem represented (R : Run G) (N p m : ℕ) :
    ∀ᶠ A : Exterior.fieldDir G (R.family.side (m + 1) p) 1 in 𝓝 0,
      flags (R.family.path.levels.budget (m + 1)).threshold
        (Precision.represent A) = ∅ ∧
      ∀ β : ℝ,
        (R.family.path.rep N p (m + 1)).path.inChannels
            (R.family.path.levels.params (m + 1)).clip
            (R.family.path.levels.budget (m + 1)) β (Precision.represent A) =
          β * Precision.mainTerm (R.family.path.levels.params (m + 1)).clip
            (R.family.path.rep N p (m + 1)).path (Precision.represent A) +
          Precision.loop (R.family.path.rep N p (m + 1)).path
            (Precision.represent A) := by
  have ht : Tendsto (Precision.represent (G := G) (n := R.family.side (m + 1) p))
      (𝓝 0) (𝓝 1) := by
    simpa only [Precision.link_one] using
      (RG02.Fk.represent_cont (G := G) (n := R.family.side (m + 1) p)).tendsto 0
  exact ht.eventually (near_identity R N p m)

end YM.Integration.ActualRunPathNeighborhood
end
