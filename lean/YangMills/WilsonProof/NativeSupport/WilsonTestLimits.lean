import YangMills.WilsonProof.NativeSupport.WilsonConstruction

set_option autoImplicit false
noncomputable section

namespace YangMills.Wilson

open Filter MeasureTheory
open scoped Topology

/-- A joint table on all arities, original Wilson labels and separated tests. -/
abbrev TestTable {g : GaugeGroup} (C : WilsonFamily g) :=
  (n : ℕ) → (Fin n → C.Token) → SeparatedTest n → ℂ

/-- Full UV limits at suitable periods followed by tested limits on one
volume sequence. The table need not be presented by a position kernel. -/
def HasTestLimits {g : GaugeGroup} (C : WilsonFamily g) (p : ℕ → ℕ)
    (L : TestTable C) : Prop :=
  ∀ (n : ℕ) (v : Fin n → C.Token) (t : SeparatedTest n),
    (∀ᶠ k : ℕ in atTop, C.suitable (p k) t) ∧ ∃ row : ℕ → ℂ,
      (∀ m, C.suitable m t → Tendsto (fun N => C.smear N m v t) atTop (𝓝 (row m))) ∧
      Tendsto (fun k => row (p k)) atTop (𝓝 (L n v t))

def RepresentsTests {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)
    (L : TestTable C) : Prop :=
  ∀ (n : ℕ) (v : Fin n → C.Token) (t : SeparatedTest n),
    L n v t = ∫ x, t x * T.correlation none (T.project ∘ v) x

/-- At each suitable period both rows are limits of the same full UV sequence.
Eventual suitability and cofinality identify their tested volume limits. -/
theorem representsTests_of_converging_refinement {g : GaugeGroup} {C : WilsonFamily g}
    {T : Hierarchy C} {p q : ℕ → ℕ} (hq : StrictMono q)
    {L : TestTable C} (original : HasTestLimits C p L)
    (chosen : C.Converges (p ∘ q) (fun v => T.correlation none (T.project ∘ v))) :
    RepresentsTests T L := by
  intro n v t
  obtain ⟨_, source, sourceUV, sourceVolume⟩ := original n v t
  obtain ⟨suitable, target, targetUV, targetVolume⟩ := chosen n v t
  have rows : (fun k => source ((p ∘ q) k)) =ᶠ[atTop] (fun k => target ((p ∘ q) k)) :=
    suitable.mono fun k hk => tendsto_nhds_unique (sourceUV _ hk) (targetUV _ hk)
  exact tendsto_nhds_unique ((sourceVolume.comp hq.tendsto_atTop).congr' rows) targetVolume

end YangMills.Wilson
