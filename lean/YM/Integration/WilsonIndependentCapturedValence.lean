import YM.Integration.WilsonIndependentFreshRoster
import YM.RegulatorIR.Sources.Roll

/-! A captured ordinary product can be reissued as a single occupied word
with a different valence ceiling. Every extra heat coefficient is zero
beyond the genuine rank bound, for both the cover and the finite board. -/
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentCapturedValence
open Finset RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Layer RegulatorIR.Budget.Packet
open RegulatorIR.Diagram RegulatorIR.Cluster RegulatorIR.Step
open scoped BigOperators Classical
variable {X Y U V : Type} {m n : ℕ}

theorem heat (K : Layer X X) (old F : Orders X) (quiet : Vacuum old)
    (ranks : Ranks m F) (orb : Bool) (larger : m ≤ n) :
    endHeat m K (logHeat K old orb) F = endHeat n K (logHeat K old orb) F := by
  classical
  let z := markHeat K (logHeat K old orb) F
  have ends := Brief.markend K old F quiet orb ranks
  funext e r
  change (∑ i ∈ range (m+3*e+1), z i e r) = ∑ i ∈ range (n+3*e+1), z i e r
  apply sum_subset (range_mono (by omega))
  intro k _ later
  simp only [mem_range,not_lt] at later
  exact ends k e (show m+3*e < k by omega) r

variable {P : ℝ} {A : Deck P X U} {B : Deck P Y V} (step : GridStep A B)

theorem cover (old F : Orders X) (quiet : Vacuum (step.jVac old)) (ranks : Ranks m F) (larger : m ≤ n) :
    step.each m old F = step.each n old F := by
  let joint := (firstChannel A B).native
  have h := heat step.line (step.jVac old) (present joint F) quiet (ranks_offer joint F ranks) false larger
  unfold GridStep.each
  rw [show (fun e r => offer (firstChannel A B).native (F e r)) = present joint F from rfl, h]

theorem finite (old F : Orders U) (quiet : Vacuum (step.jOrb old)) (ranks : Ranks m F) (larger : m ≤ n) :
    step.island m old F = step.island n old F := by
  let joint := (firstChannel A B).tile
  have h := heat step.layer (step.jOrb old) (present joint F) quiet (ranks_offer joint F ranks) true larger
  unfold GridStep.island
  rw [show (fun e r => offer (firstChannel A B).tile (F e r)) = present joint F from rfl, h]

end YM.Integration.WilsonIndependentCapturedValence
