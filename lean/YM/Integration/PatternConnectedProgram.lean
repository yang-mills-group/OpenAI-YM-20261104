import YM.Integration.PatternTensorRows
import YM.Integration.NormalizedKernelProgram
import YM.Integration.HeterogeneousTensorCoordinates

/-!
# Original connected kernels as contractions with explicit external indices

For each fixed ordered slot pattern the covariance program is fixed.
Only then are the original Gaussian indices summed. The remaining
physical indices are summed separately. All program entries and all
original normalized tensor coefficients are retained.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.PatternConnectedProgram

open Finset Function
open YM.Marker YM.Multi YM.Next.Rank
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Comparison.RG02.Cumulants YM.Comparison.RG02.Sky
open YM.Extra.Trajectories (connected)
open YM.Integration.FiniteConnectedProgram
open YM.Integration.NormalizedKernelProgram (vertex)
open scoped BigOperators Classical

variable {I J V : Type} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [Fintype V] [DecidableEq V]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (e : E) (L : (I → ℝ) →ₗ[ℝ] E) (M : (J → ℝ) →ₗ[ℝ] E)
variable (T : V → Σ n, Tensor.T E ℂ n)

abbrev Patterns := ∀ v, Fin (T v).1 → PatternTensorRows.Kind
abbrev Config (p : Patterns T) := ∀ v, PatternTensorRows.State (p v) I J

def vertexValue (B : J → ℝ) (p : Patterns T) (v : V) (z : PatternTensorRows.State (p v) I J) : ℂ :=
  PatternTensorRows.tensorValue e L M (T v).2 ⟨p v, z⟩ * PatternTensorRows.physicalWeight B ⟨p v, z⟩

def configurationSum (Q : Normal.Symmetric I) (B : J → ℝ)
    (p : Patterns T) (root : V) : ℂ :=
  ∑ j : Fin (Rig.program (fun v => PatternTensorRows.Internal (p v)) root).length,
    ∑ z : Config (I := I) (J := J) T p,
      HeterogeneousTensorCoordinates.diagram ((Rig.program (fun v => PatternTensorRows.Internal (p v)) root).get j)
        (vertexValue e L M T B p) (fun _ _ i k => Q.cov i k) z

def contractionSum (Q : Normal.Symmetric I) (B : J → ℝ)
    (p : Patterns T) (root : V) : ℂ :=
  ∑ j : Fin (Rig.program (fun v => PatternTensorRows.Internal (p v)) root).length,
    ∑ x : (Σ v, PatternTensorRows.External (p v)) → J,
      HeterogeneousTensorCoordinates.contraction ((Rig.program (fun v => PatternTensorRows.Internal (p v)) root).get j)
        (vertexValue e L M T B p) (fun _ _ i k => Q.cov i k) x

def programContraction (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) : ℂ :=
  ∑ p : Patterns T, contractionSum e L M T Q B p root

lemma program_instances {A : Type} [Fintype A] [DecidableEq A]
    (U : A → Type) (F₁ F₂ : ∀ v, Fintype (U v))
    (D₁ D₂ : ∀ v, DecidableEq (U v)) (root : A) :
    @Rig.program A _ _ U F₁ D₁ root = @Rig.program A _ _ U F₂ D₂ root := by
  have hF : F₁ = F₂ := Subsingleton.elim _ _
  have hD : D₁ = D₂ := Subsingleton.elim _ _
  cases hF
  cases hD
  rfl

private lemma stock_patterns (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) :
    stockValue Q (fun v => PatternTensorRows.rows e L M B (T v).2) root =
      ∑ p : Patterns T, configurationSum e L M T Q B p root := by
  calc
    stockValue Q (fun v => PatternTensorRows.rows e L M B (T v).2) root =
        ∑ q : Σ p : Patterns T, Config (I := I) (J := J) T p,
          ∑ j : Fin (Rig.program (fun v => PatternTensorRows.Internal (q.1 v)) root).length,
            HeterogeneousTensorCoordinates.diagram ((Rig.program (fun v => PatternTensorRows.Internal (q.1 v)) root).get j)
              (vertexValue e L M T B q.1) (fun _ _ i k => Q.cov i k) q.2 := by
      unfold stockValue
      apply Fintype.sum_equiv PatternTensorRows.piSigma
      intro a
      simp only [Finset.mul_sum, coefficient, pathValue, fieldIndex,
        PatternTensorRows.rows, HeterogeneousTensorCoordinates.diagram, vertexValue,
        PatternTensorRows.piSigma]
      let U : V → Type := fun v => PatternTensorRows.Internal (a v).1
      let evaluate : List (Rig.Record U) → ℂ := fun fs =>
        ∑ j : Fin fs.length,
          HeterogeneousTensorCoordinates.diagram (fs.get j)
            (fun v z => PatternTensorRows.tensorValue e L M (T v).2 ⟨(a v).1, z⟩ *
              PatternTensorRows.physicalWeight B ⟨(a v).1, z⟩)
            (fun _ _ i k => Q.cov i k) (fun v => (a v).2)
      change evaluate (@Rig.program V _ _ U
        (fun v => (PatternTensorRows.rows e L M B (T v).2).finiteLeg (a v))
        (fun v => Classical.decEq (U v)) root) =
          evaluate (@Rig.program V _ _ U (fun v => inferInstance)
            (fun v => inferInstance) root)
      exact congrArg evaluate (program_instances U _ _ _ _ root)
    _ = ∑ p : Patterns T, ∑ z : Config (I := I) (J := J) T p,
        ∑ j : Fin (Rig.program (fun v => PatternTensorRows.Internal (p v)) root).length,
          HeterogeneousTensorCoordinates.diagram ((Rig.program (fun v => PatternTensorRows.Internal (p v)) root).get j)
            (vertexValue e L M T B p) (fun _ _ i k => Q.cov i k) z := by
      rw [Fintype.sum_sigma]
    _ = ∑ p : Patterns T, configurationSum e L M T Q B p root := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm

private lemma sum_coordinates {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (q : α ≃ β × γ) (d : α → ℂ) :
    (∑ z, d z) = ∑ x : γ, ∑ u : β, d (q.symm (u, x)) :=
  (Equiv.sum_comp q.symm d).symm.trans
    (Fintype.sum_prod_type_right (fun y : β × γ => d (q.symm y)))

private lemma sum_fintype_eq {A : Type*} (F₁ F₂ : Fintype A) (d : A → ℂ) :
    @Finset.sum A ℂ _ (@Finset.univ A F₁) d =
      @Finset.sum A ℂ _ (@Finset.univ A F₂) d := by
  have hF : F₁ = F₂ := Subsingleton.elim _ _
  cases hF
  rfl

lemma configuration_fubini (Q : Normal.Symmetric I) (B : J → ℝ)
    (p : Patterns T) (root : V) :
    configurationSum e L M T Q B p root =
      contractionSum e L M T Q B p root := by
  unfold configurationSum contractionSum
  apply Finset.sum_congr rfl
  intro j _
  unfold HeterogeneousTensorCoordinates.contraction
  refine (sum_coordinates
    (HeterogeneousTensorCoordinates.coordinates
      (U := fun v => PatternTensorRows.Internal (p v))
      (E := fun v => PatternTensorRows.External (p v)) (I := I) (J := J))
    (HeterogeneousTensorCoordinates.diagram
      ((Rig.program (fun v => PatternTensorRows.Internal (p v)) root).get j)
      (vertexValue e L M T B p) (fun _ _ i k => Q.cov i k))).trans ?_
  apply Finset.sum_congr rfl
  intro x _
  exact sum_fintype_eq _ _ _

/-- Gaussian configurations are summed inside the contraction. Physical
external configurations and every program-list entry remain explicit. -/
theorem stock_contraction (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) :
    stockValue Q (fun v => PatternTensorRows.rows e L M B (T v).2) root =
      programContraction e L M T Q B root := by
  rw [stock_patterns]
  unfold programContraction
  apply Finset.sum_congr rfl
  intro p _
  exact configuration_fubini e L M T Q B p root

variable {R : Census V}

def modeContraction (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) : ℂ :=
  if h : t.val.Nonempty then
    programContraction e L M (fun v : t.val => T v.val) Q B ⟨h.choose, h.choose_spec⟩
  else 0

theorem cumulant_contraction (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) :
    (connected (moments R (Normal.blend Q 0)
      (fun v => Assembly.wordL (e + M B) L (T v).2))).part t =
        modeContraction e L M T Q B t := by
  have h : (fun v => Assembly.wordL (e + M B) L (T v).2) =
      fun v => (PatternTensorRows.rows e L M B (T v).2).polynomial :=
    funext (fun v => PatternTensorRows.word_rows e L M B (T v).2)
  rw [h, cumulant_program]
  unfold modeValue modeContraction
  split_ifs with ht
  · exact stock_contraction e L M (fun v : t.val => T v.val) Q B
      ⟨ht.choose, ht.choose_spec⟩
  · rfl

def HasExternal (p : Patterns T) : Prop := Nonempty (Σ v, PatternTensorRows.External (p v))

omit [Fintype I] [Fintype J] [DecidableEq V] in
private lemma diagram_zero (Q : Normal.Symmetric I) (p : Patterns T)
    (h : HasExternal T p) (f : Rig.Record (fun v => PatternTensorRows.Internal (p v)))
    (z : Config (I := I) (J := J) T p) :
    HeterogeneousTensorCoordinates.diagram f (vertexValue e L M T 0 p) (fun _ _ i k => Q.cov i k) z = 0 := by
  obtain ⟨⟨v, u⟩⟩ := h
  unfold HeterogeneousTensorCoordinates.diagram
  have hz : (∏ a, vertexValue e L M T 0 p a (z a)) = 0 := by
    apply Finset.prod_eq_zero (mem_univ v)
    unfold vertexValue
    rw [PatternTensorRows.weight_zero ⟨p v, z v⟩ ⟨u⟩, mul_zero]
  rw [hz, zero_mul]

omit [Fintype I] [Fintype J] [DecidableEq V] in
private lemma diagram_no_external (Q : Normal.Symmetric I) (B : J → ℝ)
    (p : Patterns T) (h : ¬ HasExternal T p)
    (f : Rig.Record (fun v => PatternTensorRows.Internal (p v)))
    (z : Config (I := I) (J := J) T p) :
    HeterogeneousTensorCoordinates.diagram f (vertexValue e L M T B p) (fun _ _ i k => Q.cov i k) z =
      HeterogeneousTensorCoordinates.diagram f (vertexValue e L M T 0 p) (fun _ _ i k => Q.cov i k) z := by
  unfold HeterogeneousTensorCoordinates.diagram
  apply congrArg (· * _)
  apply Finset.prod_congr rfl
  intro v _
  have he : IsEmpty (PatternTensorRows.External (p v)) := ⟨fun u => h ⟨⟨v, u⟩⟩⟩
  unfold vertexValue
  rw [PatternTensorRows.weight_empty B ⟨p v, z v⟩ he, PatternTensorRows.weight_empty 0 ⟨p v, z v⟩ he]

def centeredContraction (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) : ℂ :=
  ∑ p : Patterns T, if HasExternal T p then contractionSum e L M T Q B p root else 0

theorem program_centered (Q : Normal.Symmetric I) (B : J → ℝ) (root : V) :
    programContraction e L M T Q B root - programContraction e L M T Q 0 root =
      centeredContraction e L M T Q B root := by
  unfold programContraction centeredContraction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : HasExternal T p
  · rw [if_pos h]
    have hz : contractionSum e L M T Q 0 p root = 0 := by
      rw [← configuration_fubini]
      unfold configurationSum
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro z _
      exact diagram_zero e L M T Q p h _ z
    rw [hz, sub_zero]
  · rw [if_neg h]
    have he : contractionSum e L M T Q B p root =
        contractionSum e L M T Q 0 p root := by
      rw [← configuration_fubini, ← configuration_fubini]
      unfold configurationSum
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro z _
      exact diagram_no_external e L M T Q B p h _ z
    rw [he, sub_self]

def centeredMode (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) : ℂ :=
  if h : t.val.Nonempty then
    centeredContraction e L M (fun v : t.val => T v.val) Q B ⟨h.choose, h.choose_spec⟩
  else 0

omit [Fintype V] in
theorem mode_centered (Q : Normal.Symmetric I) (B : J → ℝ) (t : R.Mode) :
    modeContraction e L M T Q B t - modeContraction e L M T Q 0 t =
      centeredMode e L M T Q B t := by
  unfold modeContraction centeredMode
  split_ifs with h
  · exact program_centered e L M (fun v : t.val => T v.val) Q B
      ⟨h.choose, h.choose_spec⟩
  · exact sub_self 0

variable (l : Hot R → ℕ) (F : Hot R → E → ℂ) (f : E → ℝ)

theorem kernel_contraction (Q : Matrix I I ℝ) (hQ : Q.IsSymm)
    (r : ℕ) (B : J → ℝ) (t : (Board R r).Mode) :
    (connected (Assembly.prescription (e + M B) L l F f Q hQ r)).part t =
      ∑ s ∈ shards (Board R r) t,
        modeContraction e L M (vertex l F f r)
          (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s := by
  unfold Assembly.prescription
  rw [Cloud.prescribed_log]
  have h : Assembly.generator (e + M B) L l F f r =
      fun v => Assembly.wordL (e + M B) L (vertex l F f r v).2 :=
    funext (NormalizedKernelProgram.generator_word L l F f (e + M B) r)
  rw [h]
  apply Finset.sum_congr rfl
  intro s _
  exact cumulant_contraction e L M (vertex l F f r)
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s

theorem kernel_centered (Q : Matrix I I ℝ) (hQ : Q.IsSymm)
    (r : ℕ) (B : J → ℝ) (t : (Board R r).Mode) :
    (connected (Assembly.prescription (e + M B) L l F f Q hQ r)).part t -
        (connected (Assembly.prescription (e + M 0) L l F f Q hQ r)).part t =
      ∑ s ∈ shards (Board R r) t,
        centeredMode e L M (vertex l F f r)
          (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s := by
  rw [kernel_contraction, kernel_contraction, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact mode_centered e L M (vertex l F f r)
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank Q hQ) B s

end YM.Integration.PatternConnectedProgram
end
