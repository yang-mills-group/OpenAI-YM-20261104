import YM.Integration.RiderTastePresentation

/-! Exact regular and caption sums for the native polynomial ledger.
The only infinite-sum premise is summability of the original painted labels.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.RiderTastePresentation.Ledger
open Lattice Wilson RG Marker Overlay Extra.Trajectories
open RG3.Held RG3.Forms
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] {R : Census V}
    {Ω J : Type*} [Countable J] {G : Gauge} {n : Side}
    (L : Ledger Ω J G n R) (P : Rep G n)

def painted (a : Ω) (U : Config G n) (j : J) : Poly R :=
  if L.total j then L.raw a j U
  else masked P.p.threshold (L.region j) (L.raw a j) U

def regularPart (a : Ω) (U : Config G n) (j : J) : Poly R :=
  if L.total j then 0
  else masked P.p.threshold (L.region j) (L.raw a j) U

def scalarPart (a : Ω) (j : J) : Poly R :=
  if L.total j then L.raw a j 1 else 0

variable {L P} {a : Ω} {U : Config G n}

omit [Countable J] in
theorem regularPart_summable (h : Summable (L.painted P a U)) :
    Summable (L.regularPart P a U) := by
  apply (h.indicator {j | ¬ L.total j}).congr
  intro j
  by_cases ht : L.total j <;> simp [painted, regularPart, ht]

omit [Countable J] in
theorem scalarPart_summable (h : Summable (L.painted P a U))
    (hs : ∀ j, L.total j → L.raw a j U = L.raw a j 1) :
    Summable (L.scalarPart a) := by
  apply (h.indicator {j | L.total j}).congr
  intro j
  by_cases ht : L.total j
  · simp [painted, scalarPart, ht, hs j ht]
  · simp [scalarPart, ht]

omit [Countable J] in
theorem painted_split
    (hs : ∀ j, L.total j → L.raw a j U = L.raw a j 1) (j : J) :
    L.regularPart P a U j + L.scalarPart a j = L.painted P a U j := by
  by_cases ht : L.total j
  · simp only [regularPart, scalarPart, painted, if_pos ht, zero_add, hs j ht]
  · simp only [regularPart, scalarPart, painted, if_neg ht, add_zero]

variable (L P) (o : V → Site n) (span : V → Support n) [Nonempty V]

theorem regular_ray (a : Ω) (U : Config G n) (i : ℕ) :
    ((L.taste P o span).menu.terms a).ray i U =
      selectedTerm (L.covered span) (R.fire (Classical.arbitrary V))
        (L.regularPart P a U) i := by
  by_cases hc : i ∈ Set.range (pin : L.RegularKey span → ℕ)
  · obtain ⟨k, rfl⟩ := hc
    rw [selectedTerm_pin]
    simp only [Bands.ray, View.terms, taste, view, unpin_pin]
    by_cases ht : L.total k.val.1 <;>
      by_cases hu : Healthy P.p.threshold (L.region k.val.1) U <;>
      simp [regularPart, modeProjection_apply, ht, masked, hu, Poly.part_nil]
  · rw [selectedTerm_blank _ _ _ hc]
    simp only [Bands.ray, View.terms, taste, view, unpin_blank _ _ hc]
    by_cases hu : Healthy P.p.threshold Finset.univ U <;>
      simp [masked, hu, Poly.send_zero]

theorem caption_term (a : Ω) (i : ℕ) :
    Poly.send ((L.taste P o span).tag i) ((L.taste P o span).score a i) =
      selectedTerm (L.covered span) (R.fire (Classical.arbitrary V))
        (L.scalarPart a) i := by
  by_cases hc : i ∈ Set.range (pin : L.RegularKey span → ℕ)
  · obtain ⟨k, rfl⟩ := hc
    rw [selectedTerm_pin]
    simp only [taste, unpin_pin]
    by_cases ht : L.total k.val.1 <;>
      simp only [scalarPart, ht, if_true, if_false, modeProjection_apply, Poly.part_nil]
  · rw [selectedTerm_blank _ _ _ hc]
    simp only [taste, unpin_blank _ _ hc, Poly.send_zero]

/-- The encoded regular rows and scalar captions sum to the same original
quiet-free painted polynomial. Summability is inherited from that ledger. -/
theorem log_sum [Fintype V] (a : Ω) (U : Config G n)
    (h : Summable (L.painted P a U))
    (hs : ∀ j, L.total j → L.raw a j U = L.raw a j 1)
    (hg : ∀ k : Key J R, ¬ L.covered span k →
      (L.painted P a U k.1).part k.2.val = 0)
    (hq : ∀ j, (L.painted P a U j).part R.quiet = 0) :
    ((L.taste P o span).leaf a).log U = ∑' j, L.painted P a U j := by
  have hr := regularPart_summable h
  have hc := scalarPart_summable h hs
  have hgr (k : Key J R) (hk : ¬ L.covered span k) :
      (L.regularPart P a U k.1).part k.2.val = 0 := by
    by_cases ht : L.total k.1
    · simp only [regularPart, if_pos ht, Poly.part_nil]
    · simpa only [regularPart, painted, if_neg ht] using hg k hk
  have hgc (k : Key J R) (hk : ¬ L.covered span k) :
      (L.scalarPart a k.1).part k.2.val = 0 := by
    by_cases ht : L.total k.1
    · simpa only [scalarPart, painted, if_pos ht, hs k.1 ht] using hg k hk
    · simp only [scalarPart, if_neg ht, Poly.part_nil]
  have he : (∑' j, L.regularPart P a U j) + (∑' j, L.scalarPart a j) =
      ∑' j, L.painted P a U j := by
    rw [← hr.tsum_add hc]
    exact tsum_congr (painted_split hs)
  have hqsum : (∑' j, L.painted P a U j).part R.quiet = 0 := by
    rw [Poly.share h]
    simp_rw [hq]
    exact tsum_zero
  change ((∑ v : V, Poly.send (R.fire v) 0) +
      ∑' i, ((L.taste P o span).menu.terms a).ray i U) +
      (∑' i, Poly.send ((L.taste P o span).tag i) ((L.taste P o span).score a i)) = _
  simp only [Poly.send_zero, Finset.sum_const_zero, zero_add]
  simp_rw [L.regular_ray P o span a U, L.caption_term P o span a]
  rw [selected_tsum _ _ hr hgr, selected_tsum _ _ hc hgc]
  calc
    _ = ((∑' j, L.regularPart P a U j) + (∑' j, L.scalarPart a j)) -
        modeProjection R.quiet
          ((∑' j, L.regularPart P a U j) + (∑' j, L.scalarPart a j)) := by
      rw [map_add]
      abel
    _ = _ := by
      rw [he, modeProjection_apply, hqsum, Poly.send_zero, sub_zero]

end YM.Integration.RiderTastePresentation.Ledger
