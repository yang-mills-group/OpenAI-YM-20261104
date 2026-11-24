import YM.Integration.Envelope
import YM.RemainderComparison.Creek.Lilt

/-!
The supremum over test choices, healthy fields, and allowed left derivatives is
inside the coefficient budget. This module uses the same represented functions
and supports as the supplier. It does not identify arbitrary portraits with
physical multilinear insertions, nor supply the analytic admission hypotheses.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration
open Lattice Wilson RG Finset
open Push.AbsoluteSums
open RemainderComparison.WickReps
open scoped Classical

/-- Domination is applied after taking each coefficient's own supremum. -/
lemma hit_envelope {ι : Type*} [DecidableEq ι] {n : Side}
    (X : ι → Support n) (M : ℕ) {α : ι → Type*}
    (f : ∀ i, α i → ℝ) {w : ι → ℝ} {a b : ℝ}
    (hw : ∀ i, 0 ≤ w i) (hf : ∀ i x, f i x ≤ w i)
    (H : Ac.Hit X M w a b) : Ac.Hit X M (fun i => envelope (f i)) a b := by
  intro x
  apply budget_mono (H x)
  · intro i
    split
    · exact mul_nonneg (envelope_nonneg (hw i) (hf i)) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    split
    · exact mul_le_mul_of_nonneg_right (envelope_le (hw i) (hf i)) (Real.exp_pos _).le
    · exact le_rfl

/-- Every test, root, field and derivative choice allowed by the actual budget. -/
structure JetProbe {G : Gauge} {c : Side} (P : BudgetPoint) (X : Support c)
    (α : Type*) where
  test : α
  root : Site c
  root_mem : root ∈ X
  field : Config G c
  healthy : Healthy P.threshold X field
  directions : List (Directions G c)
  order : directions.length ≤ P.order
  bounded : ∀ A ∈ directions, P.dirBound root A

variable {G : Gauge} {c : Side} {ι J : Type} {α : Type*}
variable (T : Manor G c ι α J) (S : Set J) (P : BudgetPoint)

def jetValue (i : J) (v : JetProbe (G := G) P (T.halls i) α) : ℝ :=
  ‖leftDerivs (T.solvent v.test i) v.directions v.field‖

/-- The canonical coefficient seminorm, with all suprema taken before summing. -/
def jetCost (i : J) : ℝ :=
  if i ∈ S then envelope (jetValue T P i) else 0

variable {T S P} {root : ι → Support c} {a b : ℝ}

/-- An existing common majorant pays the full joint derivative/test envelope
without changing the family, supports, coupling, or numerical budget. -/
theorem spinal_jet_cost (H : T.Spinal S root P a b) :
    (∀ i, 0 ≤ jetCost T S P i) ∧
    (∀ i ∈ S, ∀ t x, x ∈ T.halls i →
      P.supBounds x (T.halls i) (T.solvent t i) (jetCost T S P i)) ∧
    Ac.Hit T.halls P.B (jetCost T S P) a b := by
  obtain ⟨w, hw, hF, hB⟩ := H.grants
  have hvalue (i : J) (hi : i ∈ S) (v : JetProbe (G := G) P (T.halls i) α) :
      jetValue T P i v ≤ w i :=
    ((hF i hi).2 v.test v.root v.root_mem).2 v.field v.healthy
      v.directions v.order v.bounded
  have hnonneg (i : J) : 0 ≤ jetCost T S P i := by
    unfold jetCost
    split
    · exact envelope_nonneg (hw i) (hvalue i ‹i ∈ S›)
    · exact le_rfl
  have hle (i : J) : jetCost T S P i ≤ w i := by
    unfold jetCost
    split
    · exact envelope_le (hw i) (hvalue i ‹i ∈ S›)
    · exact hw i
  refine ⟨hnonneg, ?_, ?_⟩
  · intro i hi t x hx
    refine ⟨hnonneg i, ?_⟩
    intro U hU ds hds hdir
    rw [jetCost, if_pos hi]
    exact le_envelope (hw i) (hvalue i hi)
      ⟨t, x, hx, U, hU, ds, hds, hdir⟩
  · intro x
    apply budget_mono (hB x)
    · intro i
      split
      · exact mul_nonneg (hnonneg i) (Real.exp_pos _).le
      · exact le_rfl
    · intro i
      split
      · exact mul_le_mul_of_nonneg_right (hle i) (Real.exp_pos _).le
      · exact le_rfl

/-- The actual masked (or globally constant) coefficient, uniformly over all
fields and tests, is bounded by the same joint jet cost. No healthy-field
restriction is imposed on the evaluation point of `wet`. -/
theorem spinal_wet_le (H : T.Spinal S root P a b)
    {i : J} (hi : i ∈ S) (t : α) (U : Config G c) :
    ‖T.wet P t i U‖ ≤ jetCost T S P i := by
  obtain ⟨_, _, hF, _⟩ := H.grants
  exact Manor.wet_le t U (hF i hi).1
    ((spinal_jet_cost H).2.1 i hi t (T.port i) (T.call i))

/-- The supremum is over the literal coefficient after its actual mask. -/
def maskedCost (T : Manor G c ι α J) (S : Set J) (P : BudgetPoint) (i : J) : ℝ :=
  if i ∈ S then envelope (fun v : α × Config G c => ‖T.wet P v.1 i v.2‖) else 0

theorem spinal_masked_cost (H : T.Spinal S root P a b) :
    (∀ i, 0 ≤ maskedCost T S P i) ∧
    (∀ i ∈ S, ∀ t U, ‖T.wet P t i U‖ ≤ maskedCost T S P i) ∧
    Ac.Hit T.halls P.B (maskedCost T S P) a b := by
  have hj := spinal_jet_cost H
  have hb (i : J) (hi : i ∈ S) (v : α × Config G c) :
      ‖T.wet P v.1 i v.2‖ ≤ jetCost T S P i := spinal_wet_le H hi v.1 v.2
  have hn (i : J) : 0 ≤ maskedCost T S P i := by
    unfold maskedCost
    split
    · exact envelope_nonneg (hj.1 i) (hb i ‹i ∈ S›)
    · exact le_rfl
  have hl (i : J) : maskedCost T S P i ≤ jetCost T S P i := by
    unfold maskedCost
    split
    · exact envelope_le (hj.1 i) (hb i ‹i ∈ S›)
    · exact hj.1 i
  refine ⟨hn, ?_, ?_⟩
  · intro i hi t U
    rw [maskedCost, if_pos hi]
    exact le_envelope (hj.1 i) (hb i hi) (t, U)
  · intro x
    apply budget_mono (hj.2.2 x)
    · intro i
      split
      · exact mul_nonneg (hn i) (Real.exp_pos _).le
      · exact le_rfl
    · intro i
      split
      · exact mul_le_mul_of_nonneg_right (hl i) (Real.exp_pos _).le
      · exact le_rfl

end YM.Integration
