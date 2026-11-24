import YM.Integration.FVA1Physical.Marked.PhysicalOwners

/-! Sum the native prices over every possible mixed-source assignment.
A finite pattern records which inputs share a host. Distinct blocks of
each pattern are assigned injectively to the countably many real vacuum
labels. The countable proof retains the native mass of each enlarged host. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Finset Push.AbsoluteSums
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {M Ω : Type} [Fintype M] [Nonempty M]

def representatives (s : M → M) := univ.image s
def group (s : M → M) (l : representatives s) := univ.filter (fun k => s k = l.val)

omit [Nonempty M] in
private theorem has_member (s : M → M) (l : representatives s) :
    ∃ j, j ∈ group s l := by
  obtain ⟨j,hj,eq⟩ := mem_image.mp l.prop
  exact ⟨j, mem_filter.mpr ⟨hj,eq⟩⟩

def head (s : M → M) (l : representatives s) := (has_member s l).choose

private noncomputable def anchorFor (π : M → ℕ) (v : ℕ) : M := Classical.epsilon (fun j => π j = v)

noncomputable def hostPattern (π : M → ℕ) (j : M) := anchorFor π (π j)

omit [Fintype M] in
private theorem original (π : M → ℕ) (j : M) : π (hostPattern π j) = π j :=
  Classical.epsilon_spec (p := (fun k => π k = π j)) ⟨j,rfl⟩

private theorem fixed (π : M → ℕ) (k : representatives (hostPattern π)) : hostPattern π k.val = k.val := by
  obtain ⟨j,_,eq⟩ := mem_image.mp k.prop
  rw [← eq]
  exact congr_arg (anchorFor π) (original π j)

def distinctHosts (π : M → ℕ) : representatives (hostPattern π) ↪ ℕ where
  toFun k := π k.val
  inj' := fun k l h => Subtype.ext ((fixed π k).symm.trans ((congr_arg (anchorFor π) h).trans (fixed π l)))

private def encode (π : M → ℕ) : Σ s : M → M, representatives s ↪ ℕ := ⟨hostPattern π,distinctHosts π⟩
private def decode (w : Σ s : M → M, representatives s ↪ ℕ) (j : M) : ℕ :=
  w.2 (⟨w.1 j,mem_image_of_mem _ (mem_univ j)⟩ : representatives w.1)

private theorem encoded : Function.Injective (encode (M:=M)) := by
  apply Function.LeftInverse.injective (g:=decode)
  intro π
  exact funext (original π)

theorem group_is_physical_fibre (π : M → ℕ) (k : representatives (hostPattern π)) :
    group (hostPattern π) k = fibre π ((distinctHosts π) k) := by
  ext j
  simp only [group,fibre,mem_filter,mem_univ,true_and]
  constructor
  · intro h
    exact (original π j).symm.trans (congr_arg π h)
  · intro h
    exact (congr_arg (anchorFor π) h).trans (fixed π k)

def patternInvoice (P : Rep G n) (S : M → Support n) (C : M → ℝ) (κ : ℝ) (s : M → M) : ℝ :=
  ∏ k : representatives s, blockInvoice P (group s k) S C (head s k) κ

/-- Assignments include every function from the finite markers to the native
vacuum labels. The resulting majorants are independent of the field and
external test. The finite overhead counts patterns of coincident hosts. -/
theorem all_host_assignments (P : Rep G n) (S : M → Support n)
    (F : Ω → M → Config G n → ℝ) (C : M → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hF : ∀ u j U, |F u j U| ≤ C j) {κ : ℝ} (hK : P.activities.KBound P.p κ) :
    ∃ bound : (s : M → M) → representatives s → ℕ → ℝ,
      (∀ s k i, 0 ≤ bound s k i) ∧
      (∀ u (π : M → ℕ) U, |∏ k : representatives (hostPattern π),
        ownerBlock P (fibre π (distinctHosts π k)) S F u (distinctHosts π k) U| ≤
        ∏ k, bound (hostPattern π) k (distinctHosts π k)) ∧
      SumBudget (fun π : M → ℕ => ∏ k : representatives (hostPattern π),
        P.p.mass (enlarged P (fibre π (distinctHosts π k)) S (distinctHosts π k))
          (bound (hostPattern π) k (distinctHosts π k))) (∑ s, patternInvoice P S C κ s) := by
  choose bound nonneg values bills using fun s : M → M => assigned_blocks_budget P (group s)
    (head s) (fun k => (has_member s k).choose_spec) S F C hC hF hK
  let mass : (Σ s : M → M, representatives s ↪ ℕ) → ℝ := fun w =>
    ∏ k, P.p.mass (enlarged P (group w.1 k) S (w.2 k)) (bound w.1 k (w.2 k))
  have prices : SumBudget mass (∑ s, patternInvoice P S C κ s) :=
    Push.Local.sumBudget_sigma (f:=mass) (a:=patternInvoice P S C κ) bills
      (budget_finite (fun s => budget_nonneg (bills s)) le_rfl)
  have final := budget_pull encode encoded prices
  refine ⟨bound,nonneg,?_,?_⟩
  · intro u π U
    simpa only [group_is_physical_fibre] using values (hostPattern π) u (distinctHosts π) U
  · simpa only [mass,encode,group_is_physical_fibre] using final

end YM.Integration.FVA1Physical.Marked
