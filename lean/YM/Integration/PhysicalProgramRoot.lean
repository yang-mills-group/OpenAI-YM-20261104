import YM.Integration.PatternConnectedProgram

/-!
# Rerooting the complete program at a retained physical port

For one fixed slot pattern the full configuration sum is the native
cumulant of fixed polynomial rows. Hence it is independent of the
program root. The anchored sum chooses an actual physical port and
uses its vertex as the root, without deleting or reweighting entries.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.PhysicalProgramRoot

open Finset Function
open YM.Marker YM.Multi YM.Next.Rank
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Comparison.RG02.Cumulants YM.Comparison.RG02.Sky
open YM.Extra.Trajectories (connected)
open YM.Integration.FiniteConnectedProgram
open YM.Integration.PatternConnectedProgram
open YM.Integration.NormalizedKernelProgram (vertex)
open scoped BigOperators Classical

variable {I J V : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (e : E) (L : (I → ℝ) →ₗ[ℝ] E) (M : (J → ℝ) →ₗ[ℝ] E)
variable (T : V → Σ n, Tensor.T E ℂ n)

def fixedRows (B : J → ℝ) (p : Patterns T) (v : V) : Rows I where
  Choice := PatternTensorRows.State (p v) I J
  finiteChoice := inferInstance
  Leg _ := PatternTensorRows.Internal (p v)
  finiteLeg _ := inferInstance
  coefficient := vertexValue e L M T B p v
  index z := z.1

private lemma fixed_stock (Q : Normal.Symmetric I) (B : J → ℝ)
    (p : Patterns T) (root : V) :
    stockValue Q (fixedRows e L M T B p) root =
      contractionSum e L M T Q B p root := by
  calc
    stockValue Q (fixedRows e L M T B p) root =
        ∑ z : Config (I := I) (J := J) T p,
          ∑ j : Fin (Rig.program (fun v => PatternTensorRows.Internal (p v)) root).length,
            HeterogeneousTensorCoordinates.diagram
              ((Rig.program (fun v => PatternTensorRows.Internal (p v)) root).get j)
              (vertexValue e L M T B p) (fun _ _ i k => Q.cov i k) z := by
      unfold stockValue
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
      let U := fun v : V => PatternTensorRows.Internal (p v)
      let evaluate := fun fs : List (Rig.Record U) =>
        ∑ j : Fin fs.length, HeterogeneousTensorCoordinates.diagram (fs.get j)
          (vertexValue e L M T B p) (fun _ _ i k => Q.cov i k) z
      change evaluate (@Rig.program V _ _ U
        (fun v => (fixedRows e L M T B p v).finiteLeg (z v))
        (fun v => Classical.decEq (U v)) root) =
          evaluate (@Rig.program V _ _ U (fun v => inferInstance)
            (fun v => inferInstance) root)
      exact congrArg evaluate (program_instances U _ _ _ _ root)
    _ = configurationSum e L M T Q B p root := Finset.sum_comm
    _ = contractionSum e L M T Q B p root := configuration_fubini e L M T Q B p root

/-- Exact rerooting holds after summing all configurations and all
entries of the original ordered program for the fixed slot pattern. -/
theorem contraction_root (Q : Normal.Symmetric I) (B : J → ℝ)
    (p : Patterns T) (root root' : V) :
    contractionSum e L M T Q B p root =
      contractionSum e L M T Q B p root' := by
  rw [← fixed_stock, ← fixed_stock]
  exact (stock_program Q (fixedRows e L M T B p) root).symm.trans
    (stock_program Q (fixedRows e L M T B p) root')

def physicalPort (p : Patterns T) (h : HasExternal T p) :
    Σ v, PatternTensorRows.External (p v) := Classical.choice h

def anchoredContraction (Q : Normal.Symmetric I) (B : J → ℝ) : ℂ :=
  ∑ p : Patterns T, if h : HasExternal T p then
    contractionSum e L M T Q B p (physicalPort T p h).1 else 0

/-- The retained physical port is explicit; its vertex is the program root. -/
theorem centered_anchor (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) :
    centeredContraction e L M T Q B root = anchoredContraction e L M T Q B := by
  unfold centeredContraction anchoredContraction
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : HasExternal T p
  · rw [if_pos h, dif_pos h]
    exact contraction_root e L M T Q B p root (physicalPort T p h).1
  · rw [if_neg h, dif_neg h]

variable {R : Census V}

def anchoredMode (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) : ℂ :=
  if t.val.Nonempty then
    anchoredContraction e L M (fun v : t.val => T v.val) Q B else 0

omit [Fintype V] in
theorem mode_anchor (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) :
    PatternConnectedProgram.centeredMode e L M T Q B t =
      anchoredMode e L M T Q B t := by
  unfold PatternConnectedProgram.centeredMode anchoredMode
  by_cases h : t.val.Nonempty
  · rw [dif_pos h, if_pos h]
    exact centered_anchor e L M (fun v : t.val => T v.val) Q B
      ⟨h.choose, h.choose_spec⟩
  · rw [dif_neg h, if_neg h]

variable (l : Hot R → ℕ) (F : Hot R → E → ℂ) (f : E → ℝ)

/-- The original centered prescription, with each surviving fixed pattern
rooted at its actual chosen physical port. -/
theorem kernel_anchored (Q : Matrix I I ℝ) (hQ : Q.IsSymm)
    (r : ℕ) (B : J → ℝ) (t : (Board R r).Mode) :
    (connected (Assembly.prescription (e + M B) L l F f Q hQ r)).part t -
        (connected (Assembly.prescription (e + M 0) L l F f Q hQ r)).part t =
      ∑ s ∈ shards (Board R r) t,
        anchoredMode e L M (vertex l F f r)
          (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s := by
  rw [PatternConnectedProgram.kernel_centered]
  apply Finset.sum_congr rfl
  intro s _
  exact mode_anchor e L M (vertex l F f r)
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s

end YM.Integration.PhysicalProgramRoot
end
