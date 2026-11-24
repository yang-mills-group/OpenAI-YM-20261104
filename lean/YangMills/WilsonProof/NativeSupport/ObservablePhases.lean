import YangMills.WilsonProof.NativeSupport.WilsonLatticeData

import YangMills.Phases
import YangMills.LatticeFields
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Distinguishing vacuum characters through the original Wilson moments. -/

set_option autoImplicit false

noncomputable section

namespace YangMills.Wilson.ObservablePhases

open Filter MeasureTheory

open scoped BigOperators Topology

variable {g : GaugeGroup} {B : Maxwell.Reference g} {C : WilsonFamily g}

theorem exists_distinguishing_word {D : WilsonData B C} {T : Hierarchy C} (law : Law D T)
    {χ ψ : T.Character} (h : χ ≠ ψ) :
    ∃ w : SeparatedWord C, read T (some χ) w.val ≠ read T (some ψ) w.val := by
  by_contra! equal
  exact h (law.separates (funext equal))

theorem double_copies_fail (T : Hierarchy C) :
    ¬ Function.Injective (fun p : T.Character × Bool => signature T p.1) := by
  intro h
  have e : (T.selected, false) = (T.selected, true) := h rfl
  exact Bool.noConfusion (congrArg Prod.snd e)

end YangMills.Wilson.ObservablePhases
