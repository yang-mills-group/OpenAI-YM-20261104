import YM.Integration.NativeTasteCoveredCofactor

/-!
# Local field updates of the actual covered cofactor

The remaining rows read both their full original supports and the final
flags there. Full-support separation therefore does not by itself make
their unmasked product invariant. An admitted fixed packet, however, fixes
the complete flag set to the union of its inventories. On that flag fiber
every remaining row is unchanged by a field update inside the distinguished
support. The exact factorization below leaves the flag-fiber indicator
visible; it proves no cofactor estimate.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeCoveredCofactorLocalUpdate
open Function Finset Lattice Wilson RG Marker Overlay
open RG3.Forms RG3.Script.Picnic LocalComparison
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] {Γ : Census V}
    {G : Gauge} {n : Side} {P : Rep G n}

/-- The literal marked-entry locality field, without unrelated activity duties. -/
def EntryReads (D : Deck Γ P) : Prop :=
  ∀ i j, UsesFinal P.p.threshold (P.activities.forced i).support
    (D.contents.entries i j)

theorem entryReads_of_active (D : Deck Γ P) (hD : D.Active) : EntryReads D :=
  hD.articles.inspects

/-- Positive relative envelopes cancel as constants. The physical entries
remain the original entries; the normalized taste is used only for its receipt. -/
theorem entryReads_of_relative {X : Type*} {o : V → Site n}
    {T : Taste X o P Γ} {p : BudgetPoint} {w : V → ℝ}
    {κ regularPrice forcedPrice : ℝ} {cost : Γ.Mode → ℝ}
    (h : RelativeBudget p T w κ cost regularPrice forcedPrice) (x : X) :
    EntryReads (T.leaf x) := by
  intro i j U W hA hF
  change T.menu.force x i j U = T.menu.force x i j W
  have hScaled := (h.budget.active x).articles.inspects i j U W hA hF
  change (cost (T.menu.marks i j))⁻¹ • T.menu.force x i j U =
    (cost (T.menu.marks i j))⁻¹ • T.menu.force x i j W at hScaled
  have hOriginal := congrArg
    (fun z : ℂ => cost (T.menu.marks i j) • z) hScaled
  simpa only [smul_smul, mul_inv_cancel₀ (h.positive (T.menu.marks i j)).ne',
    one_smul] using hOriginal

/-- The original ordered product, with only the distinguished address erased. -/
def remainingProduct (D : Deck Γ P) (U : Config G n)
    (i : ℕ) (s : Finset ℕ) : Poly Γ :=
  CoveredSignedCofactors.mixed (fun j => D.contents.each j U)
    (NativeTasteCoveredCofactor.scalarRow P U) i s

/-- Exact admission of the original packet and its distinguished address. -/
def admitted (P : Rep G n) (U : Config G n) (i : ℕ) (s : Finset ℕ) : Prop :=
  i ∈ s ∧ CoveredSignedCofactors.Pinned
    (fun j => (P.activities.forced j).support)
    (fun j => (P.activities.forced j).inventory)
    (flags P.p.threshold U) i (s.erase i)

/-- Equality away from the tails of links in the distinguished full support.
This permits arbitrary changes of those links, including a single-link update. -/
def sameOutside (X : Support n) (U W : Config G n) : Prop :=
  ∀ e : Edge (Site n), e.1 ∉ X → U e = W e

theorem admitted_iff (U : Config G n) (i : ℕ) (s : Finset ℕ) :
    admitted P U i s ↔ (P.activities.admissible P.p U s ∧ i ∈ s) := by
  have hAd :
      SectorNext.Vacuum.accounted
        (fun j => (P.activities.forced j).support)
        (fun j => (P.activities.forced j).inventory)
        (flags P.p.threshold U) s ↔ P.activities.admissible P.p U s := by
    apply iff_of_eq
    unfold SectorNext.Vacuum.accounted Activities.admissible
    congr!
  simpa only [admitted, hAd] using
    (CoveredSignedCofactors.pinned_erase_iff
      (fun j => (P.activities.forced j).support)
      (fun j => (P.activities.forced j).inventory)
      (fun j => (P.activities.forced j).inventory_sup)
      (flags P.p.threshold U) i s)

/-- A fixed admitted packet fixes ALL flags, not only its distinguished inventory. -/
theorem admitted_iff_flags {U W : Config G n} {i : ℕ} {s : Finset ℕ}
    (hU : admitted P U i s) :
    admitted P W i s ↔ flags P.p.threshold W = flags P.p.threshold U := by
  constructor
  · intro hW
    have aU := (admitted_iff U i s).mp hU
    have aW := (admitted_iff W i s).mp hW
    exact aW.1.2.symm.trans aU.1.2
  · intro h
    simpa only [admitted, h] using hU

theorem cofactor_eq_if (D : Deck Γ P) (U : Config G n)
    (i : ℕ) (s : Finset ℕ) :
    NativeTasteCoveredCofactor.cofactor D U i s =
      if admitted P U i s then remainingProduct D U i s else 0 := by
  unfold NativeTasteCoveredCofactor.cofactor
    CoveredSignedCofactors.cofactorTerm admitted remainingProduct
  split_ifs <;> rfl

/-- Native marked and unmarked rows use exactly the same final-flag restriction. -/
theorem each_eq_of_agrees (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U W : Config G n) (j : ℕ)
    (hA : Agrees (P.activities.forced j).support U W)
    (hF : (P.activities.forced j).support ∩ flags P.p.threshold U =
      (P.activities.forced j).support ∩ flags P.p.threshold W) :
    D.contents.each j U = D.contents.each j W := by
  have hBase :
      Poly.send Γ.quiet (P.activities.K j U : ℂ) =
        Poly.send Γ.quiet (P.activities.K j W : ℂ) := by
    rw [hK.reads j U W hA hF]
  have hMarks :
      (∑' k, D.contents.tagged j k U) =
        ∑' k, D.contents.tagged j k W := by
    apply tsum_congr
    intro k
    exact congrArg (Poly.send (D.contents.marks j k))
      (hD j k U W hA hF)
  exact congrArg₂ (fun a b : Poly Γ => a + b) hBase hMarks

/-- The bare product is invariant when all actual support and flag reads agree. -/
theorem remainingProduct_eq_of_agrees (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U W : Config G n) (i : ℕ) (s : Finset ℕ)
    (hA : ∀ j ∈ s.erase i, Agrees (P.activities.forced j).support U W)
    (hF : ∀ j ∈ s.erase i,
      (P.activities.forced j).support ∩ flags P.p.threshold U =
        (P.activities.forced j).support ∩ flags P.p.threshold W) :
    remainingProduct D U i s = remainingProduct D W i s := by
  unfold remainingProduct CoveredSignedCofactors.mixed
  apply prod_congr rfl
  intro j hj
  split_ifs with hji
  · exact congrArg (fun r : ℝ => Poly.bead Γ (r : ℂ))
      (hK.reads j U W (hA j hj) (hF j hj))
  · exact each_eq_of_agrees D hD hK U W j (hA j hj) (hF j hj)

/-- Physical separation must include the inspected support if no flag fiber
is fixed. This statement uses the native enlarged read footprint literally. -/
theorem remainingProduct_eq_of_inspected (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U W : Config G n) (i : ℕ) (s : Finset ℕ)
    (hA : ∀ j ∈ s.erase i,
      Agrees (inspected (P.activities.forced j).support) U W) :
    remainingProduct D U i s = remainingProduct D W i s := by
  apply remainingProduct_eq_of_agrees D hD hK U W i s
  · intro j hj
    exact agrees_mono (hA j hj) (fun _ hx => mem_union_left _ hx)
  · intro j hj
    exact flags_agree P.p.threshold U W (P.activities.forced j).support (hA j hj)

/-- On the fixed admitted flag fiber, full-support separation is sufficient. -/
theorem remainingProduct_eq_on_flag_fiber (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U W : Config G n) (i : ℕ) (s : Finset ℕ)
    (hU : admitted P U i s)
    (hOutside : sameOutside (P.activities.forced i).support U W)
    (hFlags : flags P.p.threshold W = flags P.p.threshold U) :
    remainingProduct D W i s = remainingProduct D U i s := by
  symm
  apply remainingProduct_eq_of_agrees D hD hK U W i s
  · intro j hj e he _he'
    exact hOutside e (fun hx =>
      disjoint_left.mp (hU.2.2.2.1 j hj) hx he)
  · intro j _hj
    rw [hFlags]

/-- Exact local-surgery factorization. The final flag indicator is not removed
or replaced by a free-gas condition. No positivity or price is assumed. -/
theorem cofactor_local_factorization (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U W : Config G n) (i : ℕ) (s : Finset ℕ)
    (hU : admitted P U i s)
    (hOutside : sameOutside (P.activities.forced i).support U W) :
    NativeTasteCoveredCofactor.cofactor D W i s =
      if flags P.p.threshold W = flags P.p.threshold U
      then remainingProduct D U i s else 0 := by
  rw [cofactor_eq_if]
  by_cases hFlags : flags P.p.threshold W = flags P.p.threshold U
  · rw [if_pos ((admitted_iff_flags hU).mpr hFlags), if_pos hFlags]
    exact remainingProduct_eq_on_flag_fiber D hD hK U W i s hU hOutside hFlags
  · rw [if_neg (fun hW => hFlags ((admitted_iff_flags hU).mp hW)), if_neg hFlags]

theorem sameOutside_update (X : Support n) (U : Config G n)
    (e : Edge (Site n)) (u : G.El) (he : e.1 ∈ X) :
    sameOutside X U (Function.update U e u) := by
  intro f hf
  have hfe : f ≠ e := by
    intro h
    subst f
    exact hf he
  simp only [Function.update_of_ne hfe]

/-- The exact single-link form required before applying a Haar link integral. -/
theorem cofactor_update_factorization (D : Deck Γ P) (hD : EntryReads D)
    (hK : P.activities.ForcedFamily P.p)
    (U : Config G n) (i : ℕ) (s : Finset ℕ)
    (hU : admitted P U i s) (e : Edge (Site n)) (u : G.El)
    (he : e.1 ∈ (P.activities.forced i).support) :
    NativeTasteCoveredCofactor.cofactor D (Function.update U e u) i s =
      if flags P.p.threshold (Function.update U e u) = flags P.p.threshold U
      then remainingProduct D U i s else 0 :=
  cofactor_local_factorization D hD hK U (Function.update U e u) i s hU
    (sameOutside_update _ U e u he)

end YM.Integration.NativeCoveredCofactorLocalUpdate
end
