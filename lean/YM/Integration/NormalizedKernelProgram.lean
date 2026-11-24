import YM.Integration.NativeTensorRows

/-!
# The exact normalized native kernel as an ordered connected program

The packed tensor below is the actual generator tensor. It retains the
coupling factorial, the negative vacuum sign, the normalized derivative
of order j+2, and the exceptional zero vacuum vertex at j=0. Marked
vertices retain their own original degree l and derivative order l+j.

Only the physical root is split into a coupling direction and the
supplied physical linear map. The full function being differentiated is
unchanged. Every tensor slot and every program entry remains ordered.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.NormalizedKernelProgram

open Finset Function
open YM.Marker YM.Multi YM.Next.Rank
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Comparison.RG02.Cumulants YM.Comparison.RG02.Sky
open YM.Extra.Trajectories (connected)
open YM.Integration.FiniteConnectedProgram YM.Integration.NativeTensorRows
open scoped BigOperators ContDiff Classical

variable {I J V : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {R : Census V}
variable (e : E) (L : (I → ℝ) →ₗ[ℝ] E) (M : (J → ℝ) →ₗ[ℝ] E)
variable (l : Hot R → ℕ) (F : Hot R → E → ℂ) (f : E → ℝ)

private lemma word_smul (y : E) {n : ℕ} (c : ℂ) (T : Tensor.T E ℂ n) :
    Assembly.wordL y L (c • T) = c • Assembly.wordL y L T := by
  apply Valence.Enlist.paint_inj
  intro z
  simp only [map_smul, Assembly.reading_word,
    show ∀ u : Fin n → E, (c • T) u = c • T u from fun _ => rfl]

private lemma word_neg (y : E) {n : ℕ} (T : Tensor.T E ℂ n) :
    Assembly.wordL y L (-T) = -Assembly.wordL y L T := by
  apply Valence.Enlist.paint_inj
  intro z
  simp only [map_neg, Assembly.reading_word,
    show ∀ u : Fin n → E, (-T) u = -(T u) from fun _ => rfl]

private lemma word_zero (y : E) (n : ℕ) :
    Assembly.wordL y L (0 : Tensor.T E ℂ n) = 0 := by
  apply Valence.Enlist.paint_inj
  intro z
  simp only [map_zero, Assembly.reading_word,
    show ∀ u : Fin n → E, (0 : Tensor.T E ℂ n) u = 0 from fun _ => rfl]

/-- The original normalized tensor, with its native scalar and sign.
No vertex is identified with a derivative of the same rank alone. -/
def vertex (r : ℕ) (s : Hot (Board R r)) : Σ n, Tensor.T E ℂ n :=
  let k := (Join.right s.val).val.card
  let t := Join.left s.val
  if h : t.val.Nonempty then
    ⟨l ⟨t, h⟩ + k, (k.factorial : ℂ) • Tensor.coeff (F ⟨t, h⟩) (l ⟨t, h⟩ + k) 0⟩
  else
    ⟨k + 2, if k = 0 then 0 else
      (k.factorial : ℂ) •
        (-Complex.ofRealCLM.compContinuousMultilinearMap (Tensor.coeff f (k + 2) 0))⟩

/-- Every generator is the word of precisely its original normalized tensor. -/
theorem generator_word (y : E) (r : ℕ) (s : Hot (Board R r)) :
    Assembly.generator y L l F f r s =
      Assembly.wordL y L (vertex l F f r s).2 := by
  let packedWord : (Σ n, Tensor.T E ℂ n) → Normal.poly I :=
    fun v => Assembly.wordL y L v.2
  change Assembly.generator y L l F f r s = packedWord (vertex l F f r s)
  by_cases h : (Join.left s.val).val.Nonempty
  · have hv : vertex l F f r s =
        ⟨l ⟨Join.left s.val, h⟩ + (Join.right s.val).val.card,
          (((Join.right s.val).val.card).factorial : ℂ) •
            Tensor.coeff (F ⟨Join.left s.val, h⟩)
              (l ⟨Join.left s.val, h⟩ + (Join.right s.val).val.card) 0⟩ := by
      simp only [vertex, dif_pos h]
    rw [hv]
    dsimp only [packedWord]
    simpa only [Assembly.generator, dif_pos h, Assembly.kernelJet,
      Tensor.coeff] using
        (word_smul L y (((Join.right s.val).val.card).factorial : ℂ)
          (Tensor.coeff (F ⟨Join.left s.val, h⟩)
            (l ⟨Join.left s.val, h⟩ + (Join.right s.val).val.card) 0)).symm
  · have hv : vertex l F f r s =
        ⟨(Join.right s.val).val.card + 2,
          if (Join.right s.val).val.card = 0 then 0 else
            (((Join.right s.val).val.card).factorial : ℂ) •
              (-Complex.ofRealCLM.compContinuousMultilinearMap
                (Tensor.coeff f ((Join.right s.val).val.card + 2) 0))⟩ := by
      simp only [vertex, dif_neg h]
    rw [hv]
    dsimp only [packedWord]
    by_cases hk : (Join.right s.val).val.card = 0
    · simp only [Assembly.generator, dif_neg h, Assembly.naked,
        if_pos hk, smul_zero, word_zero]
    · simp only [Assembly.generator, dif_neg h, Assembly.naked,
        if_neg hk, word_smul, word_neg, Tensor.coeff]

def kernelRows (r : ℕ) (B : J → ℝ) (s : Hot (Board R r)) : Rows I :=
  NativeTensorRows.rows e L M B (vertex l F f r s).2

theorem generator_rows (r : ℕ) (B : J → ℝ) (s : Hot (Board R r)) :
    Assembly.generator (e + M B) L l F f r s =
      (kernelRows e L M l F f r B s).polynomial :=
  (generator_word L l F f (e + M B) r s).trans
    (word_rows e L M B (vertex l F f r s).2)

/-- Exact finite degree/composition/ordered-pairing expansion, before any
absolute value, cost estimate, or subtraction of the zero field. -/
theorem kernel_program (Q : Matrix I I ℝ) (hQ : Q.IsSymm)
    (r : ℕ) (B : J → ℝ) (t : (Board R r).Mode) :
    (connected (Assembly.prescription (e + M B) L l F f Q hQ r)).part t =
      ∑ s ∈ shards (Board R r) t,
        modeValue (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ)
          (kernelRows e L M l F f r B) s := by
  unfold Assembly.prescription
  have h : Assembly.generator (e + M B) L l F f r =
      fun s => (kernelRows e L M l F f r B s).polynomial :=
    funext (generator_rows e L M l F f r B)
  rw [h]
  exact cloud_program Q hQ (kernelRows e L M l F f r B) t

section Centering

variable (T : V → Σ n, Tensor.T E ℂ n)

def tensorRows (B : J → ℝ) (v : V) : Rows I :=
  NativeTensorRows.rows e L M B (T v).2

abbrev TensorAssignment := ∀ v, Fin (T v).1 → Alphabet I J

def HasPhysical (a : TensorAssignment (I := I) (J := J) T) : Prop :=
  ∃ v, HasExternal (a v)

/-- Same ordered program with only assignments having a physical slot.
The covariance products still use every original program entry. -/
def centeredStock (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) : ℂ :=
  ∑ a : TensorAssignment (I := I) (J := J) T,
    if HasPhysical T a then
      coefficient (tensorRows e L M T B) a *
        ∑ j : Fin (Rig.program (Legs (tensorRows e L M T B) a) root).length,
          pathValue Q (tensorRows e L M T B) a
            ((Rig.program (Legs (tensorRows e L M T B) a) root).get j)
    else 0

theorem stock_centered (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) :
    stockValue Q (tensorRows e L M T B) root -
        stockValue Q (tensorRows e L M T 0) root =
      centeredStock e L M T Q B root := by
  classical
  unfold stockValue centeredStock
  unfold tensorRows NativeTensorRows.rows
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : HasPhysical T a
  · rw [if_pos h]
    have hz : coefficient (tensorRows e L M T 0) a = 0 := by
      obtain ⟨v, hv⟩ := h
      unfold coefficient
      apply Finset.prod_eq_zero (mem_univ v)
      change (T v).2 (direction e L M ∘ a v) * externalProduct 0 (a v) = 0
      rw [external_zero (a v) hv, mul_zero]
    unfold tensorRows NativeTensorRows.rows at hz
    rw [hz, zero_mul, sub_zero]
  · rw [if_neg h]
    have hc : coefficient (tensorRows e L M T B) a =
        coefficient (tensorRows e L M T 0) a := by
      apply Finset.prod_congr rfl
      intro v _
      have hv : ¬ HasExternal (a v) := fun hv => h ⟨v, hv⟩
      change (T v).2 (direction e L M ∘ a v) * externalProduct B (a v) =
        (T v).2 (direction e L M ∘ a v) * externalProduct 0 (a v)
      rw [external_absent B (a v) hv, external_absent 0 (a v) hv]
    unfold tensorRows NativeTensorRows.rows at hc
    rw [hc]
    exact sub_self _

def centeredMode (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) : ℂ :=
  if h : t.val.Nonempty then
    centeredStock e L M (fun v : t.val => T v.val) Q B ⟨h.choose, h.choose_spec⟩
  else 0

omit [Fintype V] in
theorem mode_centered (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) :
    modeValue Q (tensorRows e L M T B) t -
        modeValue Q (tensorRows e L M T 0) t =
      centeredMode e L M T Q B t := by
  classical
  unfold modeValue centeredMode
  split_ifs with h
  · exact stock_centered e L M (fun v : t.val => T v.val) Q B
      ⟨h.choose, h.choose_spec⟩
  · exact sub_self 0

end Centering

/-- Centering the original prescription deletes precisely the assignments
without a physical external slot. Vacuum vertices within the remaining
connected programs are not deleted. -/
theorem kernel_centered (Q : Matrix I I ℝ) (hQ : Q.IsSymm)
    (r : ℕ) (B : J → ℝ) (t : (Board R r).Mode) :
    (connected (Assembly.prescription (e + M B) L l F f Q hQ r)).part t -
        (connected (Assembly.prescription (e + M 0) L l F f Q hQ r)).part t =
      ∑ s ∈ shards (Board R r) t,
        centeredMode e L M (vertex l F f r)
          (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s := by
  rw [kernel_program, kernel_program, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact mode_centered e L M (vertex l F f r)
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s

end YM.Integration.NormalizedKernelProgram
end
