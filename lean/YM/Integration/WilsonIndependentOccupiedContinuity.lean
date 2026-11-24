import YM.Integration.WilsonIndependentCapturedTerminal

/-! A finite-period tagged Wick step is continuous in the complete
occupied angular field, with its original quiet, heat and mean fixed. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonIndependentOccupiedContinuity
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Budget.Tuple
open RegulatorIR.Budget.Layer RegulatorIR.Diagram RegulatorIR.Step
open scoped BigOperators Classical Topology
variable {I J Z : Type} [TopologicalSpace Z] {r s : ℕ}

private theorem sym {F : Z → Packet I r} (h : Continuous F) :
    Continuous fun z => symmetry (F z) := by
  apply continuous_pi
  intro x
  simp_rw [symmetry_at]
  fun_prop

private theorem promoted {F : Z → Packet I r} (h : Continuous F) (f : I ↪ J) :
    Continuous fun z => offer f (F z) := by
  apply continuous_pi
  intro x
  by_cases hx : x ∈ Set.range (acrossT f)
  · obtain ⟨y,rfl⟩ := hx
    simp_rw [offer_eq]
    fun_prop
  · simp_rw [offer_zero f hx]
    exact continuous_const

private theorem contraction [Fintype I] {F : Z → Packet I (r+2)} (h : Continuous F) (K : Layer I I) :
    Continuous fun z => loop (F z) K := by
  apply continuous_pi
  intro x
  simp only [loop,curve,tsum_fintype]
  fun_prop

private theorem leg [Fintype I] {F : Z → Packet I r} (h : Continuous F) (K : Layer I I) (v : Fin r) :
    Continuous fun z => ray v (F z) K := by
  apply continuous_pi
  intro x
  simp only [ray,swivel,tsum_fintype]
  fun_prop

private theorem paired [Fintype I] {F : Z → Packet I (r+1)} (h : Continuous F)
    (K : Layer I I) (old : Packet I (s+1)) :
    Continuous fun z => knot K (F z) old := by
  apply continuous_pi
  intro x
  simp only [knot,splice,lace,tsum_fintype]
  fun_prop

private theorem drafted [Fintype I] {F : Z → Packet I r} (h : Continuous F) (K : Layer I I) :
    Continuous fun z => draft K (F z) := by
  have along (l : List (Fin r)) : Continuous fun z => drawing (F z) K l := by
    induction l with
    | nil => exact h
    | cons v rest ih => exact leg ih K v
  exact sym (along (List.finRange r))

private theorem matchRow [Fintype I] (K : Layer I I) {F : Z → Ranked I}
    (h : ∀ a, Continuous fun z => F z a) (old : Ranked I) (a b q : ℕ) :
    Continuous fun z => matchTwo K (F z) old q (a,b) := by
  by_cases eq : a+b=q
  · subst q
    have row (z : Z) : matchTwo K (F z) old (a+b) (a,b) = (((a:ℝ)+1)*((b:ℝ)+1)) • symmetry (knot K (F z (a+1)) (old (b+1))) := by simp [matchTwo]
    simp_rw [row]
    exact (sym (paired (r:=a) (s:=b) (h (a+1)) K (old (b+1)))).const_smul (((a:ℝ)+1)*((b:ℝ)+1))
  · simpa [matchTwo,eq] using (continuous_const : Continuous fun _ : Z => (0 : Packet I q))

private theorem marked [Fintype I] (K : Layer I I) (quiet : ℕ → Orders I)
    {F : Z → Orders I} (incoming : ∀ e r, Continuous fun z => F z e r) :
    ∀ k e r, Continuous fun z => markHeat K quiet (F z) k e r := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k earlier =>
    cases k with
    | zero =>
      intro e r
      simpa only [markHeat_first] using incoming e r
    | succ k =>
      intro e r
      simp_rw [markHeat_next]
      have heat : Continuous fun z => heating K (markHeat K quiet (F z) k e) r := by
        exact (sym (contraction (earlier k (by omega) e (r+2)) K)).const_smul (((r:ℝ)+2)*((r:ℝ)+1)/2)
      have crosses : Continuous fun z => drift K (markHeat K quiet (F z)) quiet k e r := by
        unfold drift
        apply continuous_finsetSum
        intro split present
        have cut : split.1+split.2 = k := by simpa using present
        unfold carry
        apply continuous_finsetSum
        intro grades _
        unfold force
        apply continuous_finsetSum
        intro legs _
        exact matchRow K (fun v => earlier split.1 (by omega) grades.1 v)
          (quiet split.2 grades.2) legs.1 legs.2 r
      exact (heat.add crosses).const_smul ((k:ℝ)+1)⁻¹

theorem finiteHeat [Fintype I] (m : ℕ) (K : Layer I I) (quiet : ℕ → Orders I)
    {F : Z → Orders I} (income : ∀ e r, Continuous fun z => F z e r) (e r : ℕ) :
    Continuous fun z => endHeat m K quiet (F z) e r := by
  unfold endHeat heated
  exact continuous_finsetSum _ (fun k _ => marked K quiet income k e r)

variable {P : ℝ} {U V A B : Type} {deckA : Deck P A U} {deckB : Deck P B V}

/-- All ranks include the unit. No topology is imposed on a changing
quiet prescription since the same quiet is used throughout the limit. -/
theorem island [Fintype U] [Fintype V] (S : GridStep deckA deckB) (m : ℕ) (quiet : Orders U) :
    Continuous (S.island m quiet) := by
  apply continuous_pi
  intro e
  apply continuous_pi
  intro r
  apply continuous_pi
  intro x
  apply (continuous_apply ((acrossT (lastChannel deckA deckB).tile) x)).comp
  apply drafted
  apply finiteHeat
  intro grade rank
  apply promoted
  fun_prop

end YM.Integration.WilsonIndependentOccupiedContinuity

