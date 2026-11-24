import YM.Integration.WilsonOriginalNullInventory
import YM.Integration.WilsonMeasuredOwnerIntegrable
import YM.Trace.Physicalv2.GermStep

/-! Linear decomposition of the single original Wilson operator at an actual
displaced source. All three integrability witnesses come from the same vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullTransition
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open PhysicalNext Repeat Legato AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Transit WheelP
open QuadraticLocal QuadraticLocal.Advent Trace.Physical Trace.Physical.GermGraph WilsonMeasuredCoefficientTransport
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {m N per k i d:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
    (Ψ:∀ j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    (floor:m ≤ i) (live:i<N)
local notation "incoming" => Ψ (i+1)
local notation "F₀" => R.family.labels.level d
local notation "S₀" => R.family.localSection d
local notation "op" => R.family.path.levels.clock.op i per
local notation "scale" => ((R.family.S.block i).val:ℂ)^d
include course floor live in
theorem original (y:Site (R.family.side (i+1) per))
    (h:Coefficient F₀ (R.family.side (i+1) per)) {κ b:ℝ}
    (form:h.Format y R.family.params (incoming)) (budget:h.remBound y (incoming) κ b)
    (W:Config G (R.family.side i per)) :
    GermGraph.transition (C:=R.family) d N per i (h.density y S₀ (incoming)) W =
      (scale*(op).push (incoming).beta
        (fun U=>((incoming).eval U:ℂ)* ∑' j,h.maskedTerm (incoming) j U) W+
        (GermGraph.transition (C:=R.family) d N per i (account h (incoming))) W) +
      scale*(op).push (incoming).beta ((primary y h.x).density y S₀ (incoming)) W := by
  classical
  let f:Config G (R.family.side (i+1) per)→ℂ:=fun U=>((incoming).eval U:ℂ)* ∑' j,h.maskedTerm (incoming) j U
  let v:Config G (R.family.side (i+1) per)→ℂ:=(primary y h.x).density y S₀ (incoming)
  let z:=account h (incoming)
  have step:=QuadraticLocal.Advent.later R π Γ Ψ course (Nat.le_succ_of_le floor) live
  obtain ⟨hz,hall⟩:=WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course (Nat.le_succ_of_le floor) live
    S₀ R.family.params y h form budget
  have hv:Integrable v (prior G _):= ((primary y h.x).envelope S₀ step.truep.valid
    (primary_rem (o:=y) h.x (show 0<(1:ℝ) from zero_lt_one))
    (primary_format (H:=R.family.params) h.x)).integrableC _
  have decomp : h.density y S₀ (incoming)=(f+z)+v := by
    funext U
    rw [WilsonOriginalNullInventory.split]
    change f U + v U + z U = f U + z U + v U
    ring
  have hf : Integrable f (prior G _) := by
    have eq : f=h.density y S₀ (incoming)-v-z := by rw [decomp];abel
    rw [eq];exact (hall.sub hv).sub hz
  rw [decomp,transition_add d N per (hf.add hz) hv,transition_add d N per hf hz]
  simp only [Pi.add_apply]
  change (scale * (op).push (R.family.path.β N per (i+1)) f W + _) +
    scale*(op).push (R.family.path.β N per (i+1)) v W=_
  have beta : (incoming).beta=R.family.path.β N per (i+1) := step.beta
  rw [←beta]

end YM.Integration.WilsonOriginalNullTransition
