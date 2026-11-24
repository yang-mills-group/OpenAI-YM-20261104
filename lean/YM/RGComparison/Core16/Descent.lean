import YM.RG.History
import YM.Branch.Covariant
import YM.Progress.DIRECTED_RECIPE.Normalization

/-!
# Integration object: finite string of *actual* (tagged, normalized) StepData kernels

For every proof using the actual trajectory there is a single descent. Decorations (tree slices)
are to study the integrals, not a choice used to define the kernels.

Use `β : ℕ → ℝ` (NOT the `g` or hatted schedule) starting at the coarsest level of the
segment and reading successively finer couplings -- in particular the push at the last (coarsest)
step takes `β 1`. `Descent.weighted` starts at the literal Wilson law UNNORMALIZED. Can run this
finite calculation also for non-trajectory `β` for estimating the weak-coupling dependence;
see the history binding for when the result is the physical one, not asserting that for other β
there are representations satisfying the rest of the worker contracts.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RGComparison.Core16
open Lattice RG Tree Wilson
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

/-- A descent from `top` to the side indexed over (the root/coarse end). -/
inductive Descent (top : Side) : Side → Type
  | nil : Descent top top
  | push {c f : Side} (S : StepData c f) (F : Forest S.ratio) (previous : Descent top f) : Descent top c

namespace Descent

abbrev upβ (β : ℕ → ℝ) (i : ℕ) := β (i+1)

open MeasureTheory Filter
variable {n c f : Side}

def depth : {m : Side} → Descent n m → ℕ
  | _, .nil => 0
  | _, .push _ _ d => d.depth + 1

/-- No field or coupling dependence of this cut of variables in the path integral. -/
def Links : {m : Side} → Descent n m → Type
  | _, .nil => Empty
  | _, .push _ F d => F.Free ⊕ d.Links

def Tags : {m : Side} → Descent n m → Type
  | _, .nil => Unit
  | _, .push S _ d => S.Choices × d.Tags

instance linkType : {c : Side} → (d : Descent n c) → Fintype d.Links
  | _, .nil => (inferInstance : Fintype Empty)
  | _, .push _ F d =>
    letI := linkType d
    (inferInstance : Fintype (F.Free ⊕ d.Links))

instance tagType : {c : Side} → (d : Descent n c) → Fintype d.Tags
  | _, .nil => (inferInstance : Fintype Unit)
  | _, .push S _ d =>
    letI := tagType d
    (inferInstance : Fintype (S.Choices × d.Tags))

variable (G : Gauge)

def OK : {c : Side} → Descent n c → Prop
  | _, .nil => True
  | _, .push S _ d => S.patch.Branches S.kernel G ∧ OK d

variable {G}
section output

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- Unnormalized, with respect to probability Haar. -/
def output : {c : Side} → Descent n c → (ℕ → ℝ) →
    (Config G n → X) → Config G c → X
  | _, .nil, _, f => f
  | _, .push S _ d, β, f => S.push (β 1) (d.output (upβ β) f)

variable {S : StepData c f} {T : Forest S.ratio} {d : Descent n f}

@[simp] lemma output_push (β : ℕ → ℝ) (f : Config G n → X) :
    (push S T d).output β f = S.push (β 1) (d.output (upβ β) f) := by rw [output]

@[simp] lemma output_nil (β : ℕ → ℝ) (f : Config G n → X) : (.nil : Descent n n).output β f = f := by rw [output]

variable {U : Descent n c} (h : U.OK G) (β : ℕ → ℝ)
include h

lemma output_integrable {f : Config G n → X} (hi : Integrable f (prior G n)) :
    Integrable (U.output β f) (prior G c) := by
  induction U generalizing β with
  | nil => simpa only [output_nil] using hi
  | push S T _ ih =>
    rw [output_push]
    exact StepData.push_integrable (S.isKernel h.1 (β 1)) _ (ih h.2 _)

lemma output_integral [CompleteSpace X] {f : Config G n → X} (hi : Integrable f (prior G n)) :
    ∫ x, U.output β f x ∂prior G c = ∫ x, f x ∂prior G n := by
  induction U generalizing β with
  | nil => simp only [output_nil]
  | push S T _ ih =>
    rw [output_push]
    exact (StepData.push_integral (S.isKernel h.1 (β 1)) _ (output_integrable h.2 _ hi)).trans (ih h.2 _)

lemma output_linear [CompleteSpace X] [CompleteSpace Y] (L : X →L[ℝ] Y)
    {f : Config G n → X} (hi : Integrable f (prior G n)) :
    L ∘ U.output β f = U.output β (L ∘ f) := by
  induction U generalizing β with
  | nil => simp only [output_nil]
  | push S T _ ih =>
    rw [output_push, output_push, ← ih h.2]
    funext V
    simp only [Function.comp_apply, StepData.push, ← L.integral_comp_comm (StepData.push_slice
      (S.isKernel h.1 (β 1)) _ _ (output_integrable h.2 _ hi)), L.map_smul]

omit h in
lemma output_smul_real_const (z : ℝ) (f : Config G n → X) :
    U.output β (z • f) = z • U.output β f := by
  induction U generalizing β with
  | nil => simp only [output_nil]
  | push S T _ ih =>
    rw [output_push,output_push, ih]
    funext s
    simp only [StepData.push, Pi.smul_apply, smul_comm (_ : ℝ) z, integral_smul]

/-- Gauge covariance propagates even at discarded links outside the Taylor neighborhood. -/
lemma output_invariant {g : Config G n → X} (hi : Integrable g (prior G n)) (hg : GaugeInvariant g) :
    GaugeInvariant (U.output β g) := by
  induction U generalizing β with
  | nil => simpa only [output_nil] using hg
  | @push m i S T d ih =>
    rw [output_push]
    intro t V
    let k : Site i → G.El := t ∘ S.ratio.parent
    have hc : k ∘ S.ratio.embed = t := funext fun x => congrArg t (S.ratio.embed_parent x)
    let I := d.output (upβ β) g
    let v (U : Config G i) := S.density (β 1) U (Lattice.gauge t V) • I U
    have he (U) : v (Lattice.gauge k U) = S.density (β 1) U V • I U := by
      dsimp only [v]
      rw [show I (Lattice.gauge k U) = I U from ih h.2 (upβ β) k U]
      nth_rw 1 [← hc]
      rw [S.covary h.1]
    have hq := prior_gauge k
    have hs : Integrable v (prior G i) := StepData.push_slice (S.isKernel h.1 _) _ _
      (output_integrable h.2 (upβ β) hi)
    change (∫ U, v U ∂prior G i) = ∫ U, _ • I U ∂prior G i
    have H := integral_map hq.aemeasurable (by rw [hq.map_eq]; exact hs.aestronglyMeasurable)
    simpa only [hq.map_eq, he] using H

lemma output_positive {f : Config G n → ℝ} (hi : Integrable f (prior G n)) (hp : ∀ x, 0 < f x) (V) :
    0 < U.output β f V := by
  induction U generalizing β with
  | nil => simpa only [output_nil] using hp V
  | push S T _ ih =>
    rw [output_push]
    exact Progress.DirectedRecipe.push_strict S (β 1) h.1 (ih h.2 _) (output_integrable h.2 _ hi) _

end output
section conditional
variable (U : Descent n c) (β : ℕ → ℝ) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def weighted (g : Config G n → X) := U.output β ((bare (β U.depth) : Config G n → ℝ) • g)

def vacuum := U.output β (bare (β U.depth) : Config G n → ℝ)

def conditioned (g : Config G n → X) (V) := (U.vacuum (G := G) β V)⁻¹ • U.weighted β g V

variable {U}
lemma positive (h : U.OK G) (x) : 0 < U.vacuum (G := G) β x :=
  output_positive h _ (bare_integrable _) (fun _ => bare_pos ..) x

/-- Relative (pointwise) conditioning at the retained field. This does NOT discard vacuum in
`U.weighted`. -/
lemma uncondition (h : U.OK G) (V) (g : Config G n → X) :
    U.vacuum β V • U.conditioned β g V = U.weighted β g V := smul_inv_smul₀ (positive β h V).ne' _

@[simp] lemma weighted_unit : U.weighted β (1 : Config G n → ℝ) = U.vacuum β := by
  unfold weighted vacuum
  congr
  ext
  simp

end conditional
end Descent
end YM.RGComparison.Core16
