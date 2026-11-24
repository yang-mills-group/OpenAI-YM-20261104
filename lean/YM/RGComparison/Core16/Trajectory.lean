import YM.RGComparison.Core16.Descent
import YM.Overlay.Engine

/-!
# Use the descent in an actual trajectory (not matching by the retuned `β`)

`traversal` uses the `Levels.clock` and its kernel. `line` uses the actual `H.β`. `vacuum_eq`
is an equality of complete unnormalized densities including gas, everywhere (not just at healthy
fields). Thus can apply finite-torus tests using the bare Wilson prescription to *this* object.
-/
set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16
open Lattice RG Tree Wilson
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
open MeasureTheory Filter
variable {G : Gauge}

/-- Kept the SAME even across differentiation of a weak-coupling germ. -/
abbrev Slices (A : Levels G) (p : ℕ) := ∀ i : ℕ, Forest (A.clock.op i p).ratio

/-- Kernel doesn't depend on this choice. -/
def someSlices (A : Levels G) (p : ℕ) : Slices A p := fun i =>
  Classical.choice (Tree.select _ (A.clock.op i p).patch.odd_side)

section segment
variable {A : Levels G} {p : ℕ} (Z : Slices A p) {m N : ℕ}

def traversal (h : m ≤ N) : Descent (A.S.side N p) (A.S.side m p) :=
  Nat.decreasingInduction (motive := fun i _ => Descent (A.S.side N p) (A.S.side i p))
    (fun i _ t => Descent.push (A.clock.op i p) (Z i) t) .nil h

@[simp] lemma traversal_self : traversal (N := N) Z le_rfl = .nil := Nat.decreasingInduction_self ..

lemma traversal_push (h : m < N) : traversal Z h.le = Descent.push _ (Z m) (traversal Z h) := Nat.decreasingInduction_succ_left ..

@[simp] lemma traversal_depth (h : m ≤ N) : (traversal Z h).depth = N - m := by
  induction h using Nat.decreasingInduction with
  | self => rw [traversal_self, Nat.sub_self]; rfl
  | of_succ m hm ih => rw [traversal_push Z hm, Descent.depth, ih]; omega

lemma traversal_ok (h : m ≤ N) : (traversal Z h).OK G := by
  induction h using Nat.decreasingInduction with
  | self => rw [traversal_self]; trivial
  | of_succ m hm ih => rw [traversal_push Z hm]; exact ⟨(A.blocks m p).branches, ih⟩
end segment

section trajectory
variable (H : History G) (p m N : ℕ)

def line (i : ℕ) := H.β N p (m+i)

variable {H p m N}
lemma next_line : Descent.upβ (line H p m N) = line H p (m+1) N := by
  funext i; unfold Descent.upβ line; congr 1; omega

variable (Z : Slices H.levels p) (h : H.Selected)

include h in
lemma vacuum_eq (hw : m ≤ N) : (traversal Z hw).vacuum (G := G) (line H p m N) =
    (H.rep N p m).eval := by
  induction hw using Nat.decreasingInduction with
  | self => rw [traversal_self,Descent.vacuum,Descent.output_nil]; exact (h.starts N p).2.symm
  | of_succ m hm ih =>
    rw [traversal_push Z hm, Descent.vacuum, Descent.output_push, Descent.depth]
    rw [show line H p m N (_ + 1) = _ from congr_fun next_line ((traversal Z hm).depth)]
    rw [next_line, ← Descent.vacuum, ih, (h.steps N p m hm).1]; rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The weighted output of a physical descent uses the SAME coupled input at the next level. -/
lemma weighted_step (F : Config G (H.S.side N p) → X) (hm : m < N) :
    (traversal Z hm.le).weighted (line H p m N) F =
      (H.levels.clock.op m p).push (H.β N p (m+1))
        ((traversal Z hm).weighted (line H p (m+1) N) F) := by
  unfold Descent.weighted
  rw [traversal_push Z hm, Descent.output_push, Descent.depth]
  simp_rw [show line H p m N (_ + 1) = _ from congr_fun next_line (traversal Z hm).depth]
  rw [next_line]; rfl

include h in
lemma conditional_times (hw : m ≤ N) (F : Config G (H.S.side N p) → X) (x) :
    (H.rep N p m).eval x • (traversal Z hw).conditioned (line H p m N) F x =
      (traversal Z hw).weighted (line H p m N) F x := by
  rw [← vacuum_eq Z h hw]; exact Descent.uncondition _ (traversal_ok Z hw) ..

variable (hm : m ≤ N)
lemma bare_beta : line H p m N (traversal Z hm).depth = H.β N p N := by
  rw [traversal_depth]
  unfold line; rw [Nat.add_sub_of_le hm]

/-- Same unnormalized insertion through the whole string, readout with the physical Wilson
partition; fixed vacuum *not* dividing by another step or sector mass. -/
theorem weighted_integral (F : Config G (H.S.side N p) → ℂ) (hF : Continuous F) :
    ∫ V, (traversal Z hm).weighted (line H p m N) F V ∂prior G (H.S.side m p) =
      (partition G (H.S.side N p) (H.β N p N) : ℂ) * moment (H.β N p N) F := by
  unfold Descent.weighted
  rw [bare_beta Z hm, Descent.output_integral (traversal_ok Z hm)]
  · rw [moment_formula _ _ (continuous_integrable _ hF), ← mul_assoc]
    rw [mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne'), one_mul]
    apply integral_congr_ae
    filter_upwards with x
    exact Complex.real_smul ..
  exact ((bare_cont _).smul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include h in
theorem conditional_readout (F : Config G (H.S.side N p) → ℂ) (hF : Continuous F) :
    moment (H.β N p N) F = (partition G (H.S.side N p) (H.β N p N) : ℂ)⁻¹ * ∫ V,
      ((H.rep N p m).eval V) • (traversal Z hm).conditioned (line H p m N) F V
        ∂prior G (H.S.side m p) := by
  simp_rw [conditional_times Z h hm F, weighted_integral Z hm F hF]
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (partition_pos _).ne'), one_mul]

lemma weighted_integrable (F : Config G (H.S.side N p) → X) (hF : Continuous F) :
    Integrable ((traversal Z hm).weighted (line H p m N) F) (prior G _) :=
  Descent.output_integrable (traversal_ok Z hm) _
    (((bare_cont _).smul hF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
end trajectory
end YM.RGComparison.Core16
