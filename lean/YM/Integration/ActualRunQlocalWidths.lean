import YM.Integration.RunFormalChain

/-!
# The stored width profile of the original Run

The actual stage width is the original pre-Rolls Sheet profile pulled back
through the same calendar index. This identifies stored widths only; it does
not assert a strict loss between neighboring stages or prove the remaining
marked/Ward component and input-rescaling reserves.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunQlocalWidths

open PhysicalNext.Repeat.Legato

/-- Preserve the exact pre-block profile carried by this Run's construction. -/
theorem stored_width {G : Gauge} (R : Run G) (m : ℕ) :
    (R.family.path.levels.params m).width =
      (R.metals.p.profile (R.family.path.levels.clock.J m)).width :=
  (congrArg
    (fun profile : ℕ → RG.Stage =>
      (profile (R.family.path.levels.clock.J m)).width)
    (RunFormalChain.fromRun R).planned.stage).symm

end YM.Integration.ActualRunQlocalWidths
