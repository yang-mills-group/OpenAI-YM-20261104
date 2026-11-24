import YM.Integration.AnchoredTensorContraction
import YM.Comparison.RG02.Sky.Rig

/-!
# A spanning growth order from the native connected pairing program

Only the graph combinatorics are used here. The root remains a prescribed
vertex. Each selected edge is an original list index, keeps its orientation,
and adds one new vertex. Other edges, including loops and repeated edges,
remain available to the subsequent tensor-contraction estimate.
-/

set_option autoImplicit false

noncomputable section

namespace YM.Integration.ConnectedTensorGrowth

open YM.Integration.AnchoredTensorContraction
open YM.Comparison.RG02.Sky
open Finset

variable {V J : Type*}

private def seen [DecidableEq V] (root : V) (dst : J → V) (es : List J) :
    Finset V :=
  (root :: es.map dst).toFinset

/-- Finite directed connectedness supplies an order in which every selected
edge goes from an old vertex to a new one. No order is assumed as input. -/
theorem spanning_growth [Fintype V] (src dst : J → V) (root : V)
    (hflood : ∀ s : Finset V, root ∈ s →
      (∀ e : J, src e ∈ s → dst e ∈ s) → ∀ v : V, v ∈ s) :
    ∃ es : List J, Growth src dst root es ∧
      ∀ v : V, v ∈ root :: es.map dst := by
  classical
  have aux : ∀ n : ℕ, ∀ es : List J,
      (univ \ seen root dst es).card ≤ n →
      Growth src dst root es →
      ∃ js : List J, Growth src dst root js ∧
        ∀ v : V, v ∈ root :: js.map dst := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro es hn hg
      by_cases hfull : ∀ v : V, v ∈ seen root dst es
      · exact ⟨es, hg, fun v => List.mem_toFinset.mp (hfull v)⟩
      have hedge : ∃ e : J, src e ∈ seen root dst es ∧
          dst e ∉ seen root dst es := by
        by_contra hnone
        apply hfull
        apply hflood (seen root dst es) (by simp [seen])
        intro e he
        by_contra hd
        exact hnone ⟨e, he, hd⟩
      obtain ⟨e, he, hd⟩ := hedge
      have hmem : dst e ∈ univ \ seen root dst es :=
        mem_sdiff.mpr ⟨mem_univ _, hd⟩
      have hcomp : univ \ seen root dst (es ++ [e]) =
          (univ \ seen root dst es).erase (dst e) := by
        ext v
        simp [seen, not_or, and_left_comm, and_comm]
      have hlt : (univ \ seen root dst (es ++ [e])).card < n := by
        rw [hcomp]
        exact lt_of_lt_of_le (card_erase_lt_of_mem hmem) hn
      apply ih _ hlt (es ++ [e]) le_rfl
      exact Growth.snoc hg e (List.mem_toFinset.mp he)
        (fun hx => hd (List.mem_toFinset.mpr hx))
  exact aux _ [] le_rfl Growth.nil

/-- The original ordered pairing program supplies the growth order. Its
connectedness is the native `Traces.floods` conclusion, without a separate
tree, endpoint, or enumeration hypothesis. -/
theorem program_growth {V : Type} {U : V → Type}
    [Fintype V] [∀ v, Fintype (U v)] [DecidableEq V]
    [∀ v, DecidableEq (U v)] (root : V) (f : Rig.Record U)
    (hf : f ∈ Rig.program U root) :
    ∃ es : List (Fin f.length),
      Growth (fun j => (f.get j).1.1) (fun j => (f.get j).2.1) root es ∧
        ∀ v : V, v ∈ root :: es.map (fun j => (f.get j).2.1) := by
  apply spanning_growth
  intro s hs hstep v
  change f ∈ Traces.circle Sigma.fst univ {root}
    (Fintype.card (Sigma U)) at hf
  apply Traces.floods Sigma.fst {root} s (singleton_subset_iff.mpr hs)
    univ (Fintype.card (Sigma U)) f hf ?_ v
  intro q hq hqsrc
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hq
  subst q
  exact hstep j hqsrc

end YM.Integration.ConnectedTensorGrowth
