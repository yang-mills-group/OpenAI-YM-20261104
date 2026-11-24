import YM.Integration.QLocalBarcodeIncidence

/-! Exact signed change of a compulsory forest across different inventories.
Each input is grouped in its own true support/inventory fibers. The common
torus barcode retains the same admissible support patterns and permits all
marked spectators to be kept when its quiet amplitudes change. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalBarcodeDifference
open Function Finset Lattice Wilson RG Marker FVA1
open MergeProof MergeProof.Accent Push.AbsoluteSums
open QLocalPhysicalBirthInvoice
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} (p : BudgetPoint) (A B : Activities G n)

def value (A : Activities G n) (s : Box n) (U : Config G n) : ℂ :=
  profile A (fun i => Complex.ofReal ∘ A.K i) s U

def delta (s : Box n) (U : Config G n) := value A s U - value B s U

def Receipt (c : ℝ) : Prop :=
  ∃ b : Box n → ℝ, (∀ s, 0 ≤ b s) ∧ (∀ s U, ‖delta A B s U‖ ≤ b s) ∧
    Ac.Hit Prod.fst p.B b p.supportExponent c ∧
    ∀ U : Box n → Config G n,
      Ac.Hit Prod.fst p.B (fun s => ‖delta A B s (U s)‖) p.supportExponent c

theorem Receipt.mono {c d : ℝ} (h : Receipt p A B c) (hle : c ≤ d) : Receipt p A B d := by
  obtain ⟨b,hb,hδ,hh,hU⟩ := h
  have lift {f : Box n → ℝ} (h : Ac.Hit Prod.fst p.B f p.supportExponent c) :
      Ac.Hit Prod.fst p.B f p.supportExponent d := fun x =>
    ⟨(h x).1,(h x).2.1,(h x).2.2.trans hle⟩
  exact ⟨b,hb,hδ,lift hh,fun U => lift (hU U)⟩

private theorem one {c : ℝ} (hc : A.KBound p c) :
    ∃ b : Box n → ℝ, (∀ s, 0 ≤ b s) ∧ (∀ s U, ‖value A s U‖ ≤ b s) ∧
      Ac.Hit Prod.fst p.B b p.supportExponent c := by
  obtain ⟨b,hb,hh⟩ := hc
  have hs := Activities.summable_charge (fun i => (A.forced i).inventory_ne.mono
    (A.forced i).inventory_sup) (fun i => (hb i).1) hh
  exact ⟨barcodePrice A b,barcode_nonneg A b (fun i => (hb i).1),
    barcode_bound A b hs (fun i => (hb i).2),
    QLocalBarcodeIncidence.grouped p A b (fun i => (hb i).1) hh⟩

/-- Both actual inventories are retained and all configurations may be selected
separately in their barcode. No matching of the two Nat enumerations is used. -/
theorem paid {c d : ℝ} (hc : A.KBound p c) (hd : B.KBound p d) :
    Receipt p A B (c+d) := by
  obtain ⟨f,hf,hA,ha⟩ := one p A hc
  obtain ⟨g,hg,hB,hb⟩ := one p B hd
  have hδ s U : ‖delta A B s U‖ ≤ f s + g s :=
    (norm_sub_le ..).trans (add_le_add (hA s U) (hB s U))
  have hh : Ac.Hit Prod.fst p.B (fun s => f s+g s) p.supportExponent (c+d) := by
    intro x
    convert Push.Local.sumBudget_add (ha x) (hb x) using 1
    funext s
    split_ifs <;> ring
  refine ⟨_,fun s => add_nonneg (hf s) (hg s),hδ,hh,?_⟩
  intro U x
  apply budget_mono (hh x)
  · intro s
    split <;> positivity
  · intro s
    dsimp only
    split
    · exact mul_le_mul_of_nonneg_right (hδ s (U s)) (Real.exp_nonneg _)
    · exact le_rfl

variable {V : Type} [DecidableEq V] {Γ : Census V}

/-- The nonempty changed subsets, with every complementary spectator of
the same original admissible finite barcode pattern. -/
def forest (old change : Box n → Poly Γ) (flags : Support n) : Poly Γ :=
  ∑ s : Finset (Box n), if Pattern flags s then
    ∑ j ∈ s.powerset.erase ∅, (∏ i ∈ j, change i) * ∏ i ∈ s \ j, old i else 0

theorem field_add (f g : Box n → Poly Γ) (flags : Support n) :
    field (fun s => g s + f s) flags = field f flags + forest f g flags := by
  unfold field forest
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro s _
  unfold grid
  split
  · rw [Finset.prod_add, ← Finset.add_sum_erase _ _ (empty_mem_powerset s)]
    simp
  · simp

/-- The complete nonlinear marked field with an arbitrary common marked
family, expanded around the other genuine compulsory inventory. -/
theorem marked (F : Box n → Poly Γ) (U : Config G n) (X : Support n) :
    field (fun s => bar A Γ U s + F s) X = field (fun s => bar B Γ U s + F s) X +
      forest (fun s => bar B Γ U s + F s) (fun s => Poly.bead Γ (delta A B s U)) X := by
  rw [← field_add]
  congr 1
  funext s
  change Poly.bead Γ (value A s U) + F s =
    Poly.bead Γ (value A s U - value B s U) + (Poly.bead Γ (value B s U) + F s)
  rw [map_sub]
  abel

/-- The unmarked readout on an arbitrary chosen inventory is its actual gas,
even when the same forest contains nonzero marked spectators. -/
theorem native {c : ℝ} (hc : A.KBound p c) (F : Box n → Poly Γ)
    (hF : ∀ s, (F s).part Γ.quiet = 0) (U : Config G n) :
    (field (fun s => bar A Γ U s + F s) (RG.flags p.threshold U)).part Γ.quiet =
      (A.gas p U : ℂ) := by
  obtain ⟨b,hs,hb⟩ := Activities.K_total hc
  apply Accent.stage₀ A p U (hs.of_norm_bounded (fun i => (hb i).2 U))
  intro s
  rw [Poly.part_plus, hF s, add_zero]
  exact (Poly.part_send ..).trans (if_pos rfl)

end YM.Integration.QLocalBarcodeDifference
