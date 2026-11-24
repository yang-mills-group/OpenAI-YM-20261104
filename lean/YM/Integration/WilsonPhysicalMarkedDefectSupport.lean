import YM.Ac.Tree
import YM.RG.Masks
import YM.Push.ABSOLUTE_SUMS.Basic

/-! A short physical row sees only its own marked collar. At a fixed occupied
root the true regulated support price pays the complete sum of long rows; no
factor equal to the number of sites or to the number of rows is spent. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.Support

open Finset Lattice Wilson RG Corona Ac Push.AbsoluteSums
open scoped Classical BigOperators

variable {n : Side}

/-- A radius bound from the declared center also bounds the row about every
genuine origin on that row. -/
theorem collar {o c : Site n} {S : Support n} {r k : ℕ} (ho : o ∈ S)
    (rad : ∀ x ∈ S, separation c x ≤ r) (hk : r+r ≤ k) : S ⊆ halo k {o} := by
  intro x hx
  have toCenter : separation o c ≤ r := by rw [separation_comm]; exact rad o ho
  exact halo_spec.mpr ⟨o,mem_singleton_self o,
    (separation_triangle o c x).trans ((Nat.add_le_add toCenter (rad x hx)).trans hk)⟩

/-- Exact equality on any field healthy on the declared collar, with no
restriction on the rest of that field. Clear scalar terms retain their value. -/
theorem local_read {G : Gauge} {a : ℝ} {S C : Support n} {U : Config G n}
    (F : Config G n → ℂ) (clear : Prop) (sub : S ⊆ C) (ok : Healthy a C U) :
    (if clear then F U else masked a S F U) = F U := by
  have h : Healthy a S U := ok.mono_left sub
  rw [masked_eq _ _ _ _ h,ite_self]

/-- Restrict the actual site sum only after its weight is paid. -/
theorem selected {ι : Type} (S : ι → Support n) (B : ℕ) {σ b : ℝ} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (price : Hit S B f σ b) (o : Site n) (keep : ι → Prop)
    (owner : ∀ i, keep i → o ∈ S i) :
    SumBudget (fun i => if keep i then f i * Real.exp (σ * coverNumber B (S i)) else 0) b := by
  apply budget_mono (price o)
  · intro i
    split
    · exact mul_nonneg (hf i) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    split
    next h => rw [if_pos (owner i h)]
    next =>
      split
      · exact mul_nonneg (hf i) (Real.exp_pos _).le
      · exact le_rfl

/-- Long supports of any independent marked subfamily spend only their one
rooted exponential reserve. This is an absolute price on the full selected
sum and includes arbitrary changes of sign under the original majorant. -/
theorem long {ι : Type} (S : ι → Support n) (B : ℕ) {σ δ b : ℝ} {f : ι → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hδ : 0 ≤ δ) (price : Hit S B f (σ+δ) b) (o : Site n)
    (keep : ι → Prop) (owner : ∀ i, keep i → o ∈ S i) (k : ℕ)
    (length : ∀ i, keep i → k ≤ coverNumber B (S i)) :
    SumBudget (fun i => if keep i then f i * Real.exp (σ * coverNumber B (S i)) else 0)
      (Real.exp (-δ * k) * b) := by
  let a := Real.exp (-δ * k)
  let F (i : ι) := if keep i then f i * Real.exp ((σ+δ) * coverNumber B (S i)) else 0
  have ha : 0 ≤ a := (Real.exp_pos _).le
  have hF : SumBudget F b := selected S B hf price o keep owner
  have scaled : SumBudget (fun i => a * F i) (a*b) :=
    ⟨fun i => mul_nonneg ha (hF.1 i),hF.2.1.mul_left a, by
      rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hF.2.2 ha⟩
  apply budget_mono scaled
  · intro i
    split
    · exact mul_nonneg (hf i) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    by_cases yes : keep i
    · simp only [yes,if_pos,F,a]
      have hki : (k:ℝ) ≤ coverNumber B (S i) := by exact_mod_cast length i yes
      have exp_le : Real.exp (σ * coverNumber B (S i)) ≤
          Real.exp (-δ * k) * Real.exp ((σ+δ) * coverNumber B (S i)) := by
        rw [← Real.exp_add,Real.exp_le_exp]
        nlinarith [mul_nonneg hδ (sub_nonneg.mpr hki)]
      calc
        _ ≤ f i * (Real.exp (-δ * k) * Real.exp ((σ+δ) * coverNumber B (S i))) :=
          mul_le_mul_of_nonneg_left exp_le (hf i)
        _ = _ := by ring
    · simp [yes,F]

end YM.Integration.WilsonPhysicalMarkedDefect.Support

