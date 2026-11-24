import YM.Trace.Physicalv2.GermGraph

/-! The neutral part of a capture has coefficient one. Only the signed difference from
the genuine germ-normalized incoming column is transported back through an older interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalGermReturn
open Function Filter Lattice Wilson RG Source Labels ProjectorNext.Equivariance
open Trace.Physical.GermGraph
open scoped BigOperators Classical

section Linear
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def back (frame : ℕ → E ≃ₗ[ℂ] E) (a b : ℕ) (v : E) : E :=
  frame b ((frame a).symm v)

def excess (frame : ℕ → E ≃ₗ[ℂ] E) (x : ℕ → E) (i : ℕ) : E :=
  x i - frame i ((frame (i+1)).symm (x (i+1)))

private theorem difference (frame : ℕ → E ≃ₗ[ℂ] E) (x : ℕ → E) (i b : ℕ) :
    back frame i b (excess frame x i) = back frame i b (x i) - back frame (i+1) b (x (i+1)) := by
  simp only [back, excess, map_sub, LinearEquiv.symm_apply_apply]

omit [Module ℂ E] in
private theorem sum_steps (x : ℕ → E) (n : ℕ) :
    ∑ i ∈ Finset.range n, (x i - x (i+1)) = x 0 - x n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; abel

theorem returned (frame : ℕ → E ≃ₗ[ℂ] E) (x : ℕ → E) (a n : ℕ) :
    back frame a (a+n) (x a) = x (a+n) +
      ∑ i ∈ Finset.range n, back frame (a+i) (a+n) (excess frame x (a+i)) := by
  have total : ∑ i ∈ Finset.range n, back frame (a+i) (a+n) (excess frame x (a+i)) =
      back frame a (a+n) (x a) - x (a+n) := by
    simp only [difference]
    simpa only [Nat.add_zero, Nat.add_assoc, back, LinearEquiv.apply_symm_apply] using
      sum_steps (fun i => back frame (a+i) (a+n) (x (a+i))) n
  rw [total]
  abel
end Linear

variable {G : Gauge} {C : Family G} (d N p : ℕ) (honest : C.Makes)

def frame (i : ℕ) : C.label d ≃ₗ[ℂ] C.label d :=
  if live : i ≤ N then
    if opened : Opened C d i p then fitting d N p i honest opened live else LinearEquiv.refl ℂ _
  else LinearEquiv.refl ℂ _

theorem reads_entry (i : ℕ) (live : i ≤ N) (opened : Opened C d i p) (v : C.label d) :
    frame d N p honest i v = page d p i ((C.factory d N p).entries i v) := by
  simpa only [frame, dif_pos live, dif_pos opened] using fitting_apply d N p i honest opened live v

/-- Every posted terminal vector gives zero excess on the whole middle interval. -/
theorem on_column (i : ℕ) (live : i+1 ≤ N) (lo : Opened C d i p)
    (hi : Opened C d (i+1) p) (v : C.label d) :
    excess (frame d N p honest)
      (fun s => page d p s ((C.factory d N p).entries s v)) i = 0 := by
  rw [excess, ←reads_entry d N p honest i (by omega) lo,
    ←reads_entry d N p honest (i+1) live hi, LinearEquiv.symm_apply_apply, sub_self]

/-- The source may be a newly merged signed marked packet. Each subtraction uses the very same
incoming germ, fitted at the genuine cutoff and period, before its earlier return. -/
theorem measured (a n : ℕ) (live : a+n ≤ N)
    (open_at : ∀ i, a ≤ i → i ≤ a+n → Opened C d i p)
    (q : (i : ℕ) → Coefficient (C.labels.level d) (C.side i p)) :
    let chart := frame d N p honest
    let x := fun i => page d p i (q i)
    back chart a (a+n) (x a) = x (a+n) +
      ∑ i ∈ Finset.range n, back chart (a+i) (a+n) (excess chart x (a+i)) ∧
    ∀ i, a ≤ i → i < a+n →
      let v := (chart (i+1)).symm (x (i+1))
      page d p (i+1) ((C.factory d N p).entries (i+1) v) = x (i+1) ∧
      excess chart x i = x i - page d p i ((C.factory d N p).entries i v) := by
  dsimp only
  refine ⟨returned (frame d N p honest) (fun i => page d p i (q i)) a n, ?_⟩
  intro i ha hb
  have h₀ := reads_entry d N p honest i (by omega) (open_at _ ha (by omega))
  have h₁ := reads_entry d N p honest (i+1) (by omega) (open_at _ (by omega) (by omega))
  constructor
  · rw [← h₁, LinearEquiv.apply_symm_apply]
  · rw [excess, ← h₀]

end YM.Integration.WilsonMatrixOriginalGermReturn
