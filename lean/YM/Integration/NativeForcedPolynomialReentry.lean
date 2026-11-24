import YM.Integration.OriginalForcedAddresses

/-!
Finite polynomial corrections re-enter the original activity dictionary.
The old Nat-indexed K is retained in full.  Barcode aggregation controls the
entire gas polynomial, including mixed marker coefficients.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativeForcedPolynomialReentry
open Finset Function Set MeasureTheory Lattice Wilson RG
open MergeProof MergeProof.Accent Marker Extra.Histories Planned.GuardedAtom
open PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {P : Rep G n}
    {V Y : Type*} [DecidableEq V] {B : Census V}

def rebook (K : Guard.Keeper P.p P.activities)
    (F : Box n → Y → Poly B) : ℕ → Y → Poly B :=
  extend (cart K) (F ∘ Subtype.val) 0

theorem at_address (K : Guard.Keeper P.p P.activities)
    (F : Box n → Y → Poly B) (s : StockTag n) :
    rebook K F (cart K s) = F s.val :=
  (cart K).injective.extend_apply ..

theorem off_address (K : Guard.Keeper P.p P.activities)
    (F : Box n → Y → Poly B) {i : ℕ}
    (hi : i ∉ Set.range (cart K)) : rebook K F i = 0 :=
  extend_apply' _ _ _ hi

theorem aggregate (K : Guard.Keeper P.p P.activities)
    (F : Box n → Y → Poly B) (hF : ∀ s, ¬ Sure s → F s = 0) (y : Y) :
    cram (barcode P.activities) (fun i => rebook K F i y) = fun s => F s y := by
  funext s
  rw [expand_eq]
  by_cases hs : Sure s
  · let tag : StockTag n := ⟨s, hs⟩
    rw [tsum_eq_single (cart K tag)]
    · rw [if_pos (cardK K tag), at_address]
    intro i hi
    split_ifs with hb
    · apply congrFun (off_address K F ?_) y
      rintro ⟨other, rfl⟩
      exact hi (congrArg (cart K) (Subtype.ext ((cardK K other).symm.trans hb)))
    · rfl
  · rw [congrFun (hF s hs) y]
    refine (tsum_congr ?_).trans tsum_zero
    intro i
    split_ifs with hb
    · apply congrFun (off_address K F ?_) y
      rintro ⟨tag, rfl⟩
      exact hs (((cardK K tag).symm.trans hb) ▸ tag.property)
    · rfl

theorem summable (K : Guard.Keeper P.p P.activities)
    (F : Box n → Y → Poly B) (y : Y) :
    Summable (fun i => rebook K F i y) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range (cart K)).subset
  intro i hi
  by_contra hn
  exact hi (congrFun (off_address K F hn) y)

theorem price_summable (K : Guard.Keeper P.p P.activities)
    (F : Box n → Y → Poly B) (w : V → ℝ) (y : Y) :
    Summable (fun i => Poly.price w (rebook K F i y)) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_range (cart K)).subset
  intro i hi
  by_contra hn
  apply hi
  change Poly.price w (rebook K F i y) = 0
  rw [congrFun (off_address K F hn) y]
  change Poly.price w (0 : Poly B) = 0
  exact Poly.zero_price

/-- The same common coefficient envelope survives re-entry, at exactly the
same support exponent and price.  The type Y may contain all independent tests. -/
theorem towed (K : Guard.Keeper P.p P.activities)
    (F : Box n → Y → Poly B) {w : V → ℝ} {d C : ℝ}
    (h : Towed w Prod.fst F P.p.B d C) :
    Towed w (fun i => (P.activities.forced i).support) (rebook K F) P.p.B d C := by
  obtain ⟨a, _, hH, hL⟩ := h
  let b : ℕ → ℝ := extend (cart K) (a ∘ Subtype.val) 0
  have hb (s : StockTag n) : b (cart K s) = a s.val :=
    (cart K).injective.extend_apply ..
  have hz (i : ℕ) (hi : i ∉ Set.range (cart K)) : b i = 0 :=
    extend_apply' _ _ _ hi
  have hsum : Summable b := by
    apply summable_of_hasFiniteSupport
    apply (Set.finite_range (cart K)).subset
    intro i hi
    by_contra hn
    exact hi (hz i hn)
  refine ⟨b, hsum, ?_, ?_⟩
  · intro x
    apply Push.Local.sumBudget_pass (cart K) _
    · simp_rw [hb, show ∀ s : StockTag n,
        (P.activities.forced (cart K s)).support = s.val.1 from
          fun s => congrArg Prod.fst (cardK K s)]
      exact Push.Local.sumBudget_subtype _ (hH x)
    · intro i hi
      simp [hz i hi]
  intro i
  by_cases hi : i ∈ Set.range (cart K)
  · obtain ⟨s, rfl⟩ := hi
    rw [at_address, hb]
    exact hL s.val
  rw [off_address K F hi, hz i hi]
  refine ⟨0, le_rfl, ?_, ?_⟩
  · intro y q
    simp
  simp [Push.GridApprox.Nil.wordsPrice]

variable (K : Guard.Keeper P.p P.activities)
    (F : Box n → Config G n → Poly B)

/-- Each original K stays at its original Nat address; only the finite
correction is inserted at the already available cart addresses. -/
def inserted (U : Config G n) (i : ℕ) : Poly B :=
  Poly.bead B (P.activities.K i U : ℂ) + rebook K F i U

def gas (U : Config G n) : Poly B :=
  ∑' s : Finset ℕ, if P.activities.admissible P.p U s then
    ∏ i ∈ s, inserted K F U i else 0

/-- A quiet-zero correction preserves the quiet coefficient at every original
Nat address, including all old nonzero K entries. -/
theorem inserted_quiet (h0 : ∀ s U, (F s U).part B.quiet = 0)
    (U : Config G n) (i : ℕ) :
    (inserted K F U i).part B.quiet = (P.activities.K i U : ℂ) := by
  by_cases hi : i ∈ Set.range (cart K)
  · obtain ⟨s, rfl⟩ := hi
    simp [inserted, at_address, h0, Poly.bead]
  simp [inserted, off_address K F hi, Poly.bead]

variable {e k : ℝ} (hP : P.activities.Valid P.p e k)
    {w : V → ℝ} (hw : ∀ v, 0 < w v)

include hP in
private theorem base_price_summable (U : Config G n) :
    Summable (fun i => Poly.price w (Poly.bead B (P.activities.K i U : ℂ))) := by
  simp only [Poly.bead, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
  exact (Accent.mass_crest _ hP U).norm

include hP hw in
theorem inserted_price_summable (U : Config G n) :
    Summable (fun i => Poly.price w (inserted K F U i)) := by
  exact ((base_price_summable hP U).add (price_summable K F w U)).of_nonneg_of_le
    (fun i => Poly.nonnegative hw _) (fun i => Poly.addition hw _ _)

include hP hw in
theorem inserted_profile (hF : ∀ s, ¬ Sure s → F s = 0) (U : Config G n) :
    cram (barcode P.activities) (inserted K F U) =
      fun s => bar P.activities B U s + F s U := by
  let f : ℕ → Poly B := fun i => Poly.bead B (P.activities.K i U : ℂ)
  have hf : Summable f :=
    (Poly.budgeted hw (base_price_summable hP U) (fun _ => le_rfl)).1
  have hg := summable K F U
  funext s
  change tsum (fun address : {j // barcode P.activities j = s} =>
    f (Subtype.val address) + rebook K F (Subtype.val address) U) = _
  have hf' : Summable (fun address : {j // barcode P.activities j = s} =>
      f (Subtype.val address)) := hf.comp_injective Subtype.val_injective
  have hg' : Summable (fun address : {j // barcode P.activities j = s} =>
      rebook K F (Subtype.val address) U) := hg.comp_injective Subtype.val_injective
  rw [hf'.tsum_add hg']
  have hcor : tsum (fun address : {j // barcode P.activities j = s} =>
      rebook K F (Subtype.val address) U) =
      F s U := congrFun (aggregate K F hF U) s
  rw [hcor]
  apply congrArg (· + F s U)
  ext i
  rw [Poly.share hf']
  unfold bar profile cram
  by_cases hi : i = B.quiet <;> simp [f, Poly.bead, hi]

include hP hw in
/-- Complete equality, before extracting any coefficient or integrating. -/
theorem gas_eq (hF : ∀ s, ¬ Sure s → F s = 0) (U : Config G n) :
    gas K F U = field (fun s => bar P.activities B U s + F s U)
      (flags P.p.threshold U) := by
  unfold gas
  rw [← Accent.rock_out P.activities P.p U (inserted K F U) hw
    (inserted_price_summable K F hP hw U), inserted_profile K F hP hw hF U]

include hP hw in
/-- The full gas keeps exactly the original vacuum coefficient. -/
theorem gas_quiet (hF : ∀ s, ¬ Sure s → F s = 0)
    (h0 : ∀ s U, (F s U).part B.quiet = 0) (U : Config G n) :
    (gas K F U).part B.quiet = (P.activities.gas P.p U : ℂ) := by
  rw [gas_eq K F hP hw hF U]
  apply Accent.stage₀ P.activities P.p U (Accent.mass_crest _ hP U)
  intro s
  simp [bar, Poly.bead, h0]

theorem flow_zero (o : V → Site n) (hF : ∀ s, Flow o s (F s) P.p.threshold)
    (s : Box n) (hs : ¬ Sure s) : F s = 0 := by
  funext U
  by_contra hn
  exact hs ((hF s).permits U hn).2

/-- The actual next representative supplies its own Keeper and original K.
No finite-support hypothesis on that old K is used. -/
theorem actual_gas_eq (R : Run G) (hG : G.Simple) (N m p : ℕ) (hm : m < N)
    (o : V → Site (R.family.side (m+1) p))
    (F : Box (R.family.side (m+1) p) →
      Config G (R.family.side (m+1) p) → Poly B)
    (hF : ∀ s, Flow o s (F s) (R.family.path.rep N p (m+1)).p.threshold)
    (U : Config G (R.family.side (m+1) p)) :
    gas (OriginalForcedAddresses.actual_keeper R hG N (m+1) p
      (Nat.succ_le_of_lt hm)) F U =
      field (fun s => bar (R.family.path.rep N p (m+1)).activities B U s + F s U)
        (flags (R.family.path.rep N p (m+1)).p.threshold U) := by
  exact gas_eq _ F
    (R.makes.wilson.represents N p (m+1) (Nat.succ_le_of_lt hm)).good.labels
    (w := fun _ => 1) (fun _ => zero_lt_one) (flow_zero F o hF) U

end YM.Integration.NativeForcedPolynomialReentry
