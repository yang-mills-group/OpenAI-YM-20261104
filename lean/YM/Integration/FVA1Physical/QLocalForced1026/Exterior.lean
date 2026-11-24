import YM.SectorNext.VACUUM_NORMALIZATION.Covered
import YM.QuadraticLocal.Manifold
import YM.Push.ABSOLUTE_SUMS.Array

/-!
# qlocal: rooted compulsory exteriors

The sign of neither the labels nor the cofactor with some labels starred will
be needed. Sum *all multiplicities* of companion rows, with their original
absolute support weights. The summation includes the far gas and needs no
collar or upper bound on the number of flags. Keep the rest of the exact
inventory **inside**, as a function of the same field. (If one instead makes
an independent choice of field for every whole gas product, this estimate does
not apply. It is the individual `Hard.Paid` which gives such arbitrary draws
in the activity norm.) We also inflate every *additional* forced activity by
`u ≥ 0` (in applications at least 1). `cover_power` can even afford `u = v⁻¹`,
for `v > 0` the total per-site budget. This separates mass having to use
extra hard companions from plain single-host mass.

These weights are for *coefficients of the represented polymer gas*. Keep them
distinct from absolute values of probabilities or of conditional kernels with
gas in the denominator. In particular we do **not** integrate the scalar
exp(action) divided by the vacuum partition function as if it were a
probability. Supports use `B` and the real torus `coverNumber` of the physical
step; the only product here uses the product of component weights (not a
connected norm on the union of disconnected polymers).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.QLocalForced1026

open Finset MeasureTheory Lattice RG YM.Wilson Marker QuadraticLocal Ac
open SectorNext.Vacuum Push.AbsoluteSums
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} (A : Activities G n) (p : BudgetPoint) (a : ℝ)

/-- Same convention as `p.mass`, at the displayed support exponent `a`. -/
def withSupport (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  f i * Real.exp (a * coverNumber p.B (A.forced i).support)

theorem withSupport_native (f : ℕ → ℝ) (i : ℕ) :
    withSupport A p p.supportExponent f i = p.mass (A.forced i).support (f i) := mul_comm _ _

theorem withSupport_nonneg {f : ℕ → ℝ} (nn : ∀ i, 0 ≤ f i) (i : ℕ) :
    0 ≤ withSupport A p a f i := mul_nonneg (nn i) (Real.exp_nonneg _)

/-- One rooted (site hit) price. -/
def leader (f : ℕ → ℝ) (x : Site n) (i : ℕ) : ℝ :=
  if x ∈ (A.forced i).support then withSupport A p a f i else 0

theorem leader_nonneg {f : ℕ → ℝ} (nn : ∀ i, 0 ≤ f i) (x : Site n) (i : ℕ) :
    0 ≤ leader A p a f x i := by
  unfold leader
  split <;> first | exact withSupport_nonneg A p a nn i | exact le_rfl

variable (u : ℝ)

/-- Absolute term majorant for the exterior, including the empty exterior when
possible. No factor for `L` here. -/
def restMajorant (f : ℕ → ℝ) (L : Finset ℕ) (U : Config G n) (s : Finset ℕ) : ℝ :=
  if Disjoint L s ∧ A.admissible p U (L ∪ s) then ∏ k ∈ s, u * withSupport A p a f k else 0

theorem restMajorant_nonneg (hu : 0 ≤ u) {f : ℕ → ℝ} (nn : ∀ i, 0 ≤ f i)
    (L : Finset ℕ) (U : Config G n) (s : Finset ℕ) : 0 ≤ restMajorant A p a u f L U s := by
  unfold restMajorant
  split
  · exact prod_nonneg fun j _ => mul_nonneg hu (withSupport_nonneg A p a nn j)
  exact le_rfl

theorem admits_leader_inventory {L : Finset ℕ} {s : Finset ℕ} {U : Config G n}
    (h : A.admissible p U (L ∪ s)) : (L.biUnion fun i => (A.forced i).inventory) ⊆ flags p.threshold U := by
  intro x hx
  rw [← h.2]
  obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
  exact mem_biUnion.mpr ⟨i, mem_union_left _ hi, hx⟩

theorem rest_off {L : Finset ℕ} {U : Config G n} (off : ¬ (L.biUnion fun i => (A.forced i).inventory) ⊆ flags p.threshold U)
    (f : ℕ → ℝ) (s : Finset ℕ) : restMajorant A p a u f L U s = 0 :=
  if_neg fun h => off (admits_leader_inventory A p h.2)

/-- Exact exterior re-summation set after designating any number of owners. -/
theorem accounted_as_admissible_tail {L s : Finset ℕ} {U : Config G n} (d : Disjoint L s)
    (h : A.admissible p U (L ∪ s)) :
    accounted (fun k => (A.forced k).support) (fun k => (A.forced k).inventory)
      (flags p.threshold U \ (L.biUnion fun i => (A.forced i).inventory)) s := by
  constructor
  · intro i hi j hj he
    exact h.1 (mem_union_right _ hi) (mem_union_right _ hj) he
  · -- `accounted` uses classical DecidableEq for the inventory union
    apply Eq.trans (b := (s.biUnion fun i => (A.forced i).inventory))
    · congr!
    rw [← h.2]
    ext x
    simp only [mem_sdiff, mem_biUnion]
    constructor
    · rintro ⟨i, hi, hx⟩
      refine ⟨⟨i, mem_union_right _ hi, hx⟩, ?_⟩
      rintro ⟨j, hj, hy⟩
      have ne : j ≠ i := fun eq => disjoint_left.mp d hj (eq.symm ▸ hi)
      exact disjoint_left.mp (h.1 (mem_union_left _ hj) (mem_union_right _ hi) ne)
        ((A.forced j).inventory_sup hy) ((A.forced i).inventory_sup hx)
    rintro ⟨⟨i, hi, hx⟩, off⟩
    exact ⟨i, (mem_union.mp hi).resolve_left (fun hl => off ⟨i, hl, hx⟩), hx⟩

/-- All additional inventories at fixed field. If there are flags outside
these owners, can retain one factor even before de-inflating. -/
theorem restMajorant_budget (hu : 0 ≤ u) {f : ℕ → ℝ} (nn : ∀ i, 0 ≤ f i) {v : ℝ}
    (hit : ∀ x, SumBudget (leader A p a f x) v) (gate : u*v ≤ 1)
    (L : Finset ℕ) (U : Config G n) :
    let D := flags p.threshold U \ (L.biUnion fun i => (A.forced i).inventory)
    SumBudget (restMajorant A p a u f L U) (if D = ∅ then 1 else u*v) := by
  classical
  intro D
  let X := fun k => (A.forced k).support
  let Z := fun k => (A.forced k).inventory
  let b := fun k => u * withSupport A p a f k
  have sub : ∀ k, Z k ⊆ X k := fun k => (A.forced k).inventory_sup
  have ne : ∀ k, (Z k).Nonempty := fun k => (A.forced k).inventory_ne
  have pos (k) : 0 ≤ b k := mul_nonneg hu (withSupport_nonneg A p a nn k)
  apply budget_of_sum (restMajorant_nonneg A p a u hu nn L U)
  intro S
  let live (s : Finset ℕ) := Disjoint L s ∧ A.admissible p U (L ∪ s)
  let F := S.filter live
  let I := S.biUnion id
  have incl : F ⊆ I.powerset.filter (accounted X Z D) := by
    intro s hs
    obtain ⟨sS, (ok : live s)⟩ := mem_filter.mp hs
    refine mem_filter.mpr ⟨mem_powerset.mpr fun j hj =>
      mem_biUnion.mpr ⟨s, sS, hj⟩, ?_⟩
    apply (accounted_as_admissible_tail A p ok.1 ok.2)
  have hits (x : Site n) (T : Finset ℕ) :
      (∑ j ∈ T, if x ∈ Z j then b j * Real.exp (0 * ((Z j).card:ℝ)) else 0) ≤ u*v := by
    apply le_trans _ (budget_sum (budget_scale hu (hit x)) T)
    refine sum_le_sum fun j _ => ?_
    split
    · rename_i hx
      rw [zero_mul, Real.exp_zero, mul_one, leader, if_pos (sub j hx)]
    exact (budget_scale hu (hit x)).1 j
  calc
    _ = ∑ s ∈ F, restMajorant A p a u f L U s := by
      symm
      exact sum_subset (filter_subset ..) fun s hs off => if_neg fun h => off (mem_filter.mpr ⟨hs,h⟩)
    _ = ∑ s ∈ F, ∏ j ∈ s, b j := sum_congr rfl fun s hs => if_pos (mem_filter.mp hs).2
    _ ≤ ∑ s ∈ I.powerset.filter (accounted X Z D), ∏ j ∈ s, b j :=
      sum_le_sum_of_subset_of_nonneg incl fun s _ _ => prod_nonneg fun j _ => pos j
    _ ≤ _ := by
      have he := cover_power (γ := 0) X Z sub ne gate b pos ?hits D I
      · simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at he
        convert he using 1; congr!
      case hits =>
        intro x T
        convert hits x T using 1; congr!

/-- Product of rooted budgets (keeps tuple multiplicity). As in
`Marked.host_product_budget`, here also at a dependent type of receipts. -/
theorem budget_pi {α : Type*} [Fintype α] {β : α → Type*} (f : ∀ j, β j → ℝ)
    {c : α → ℝ} (h : ∀ j, SumBudget (f j) (c j)) :
    SumBudget (fun i : ∀ j, β j => ∏ j, f j (i j)) (∏ j, c j) := by
  classical
  apply budget_of_sum (fun i => prod_nonneg (fun j _ => (h j).1 _))
  intro E
  let X := fun j => E.image (fun i => i j)
  have sub : E ⊆ Fintype.piFinset X := fun _ hi =>
    Fintype.mem_piFinset.mpr (fun _ => mem_image_of_mem _ hi)
  apply (sum_le_sum_of_subset_of_nonneg sub
    (fun i _ _ => prod_nonneg (fun j _ => (h j).1 _))).trans
  rw [← Finset.prod_univ_sum X f]
  exact prod_le_prod (fun j _ => sum_nonneg fun _ _ => (h j).1 _)
    (fun j _ => budget_sum (h j) _)

theorem leader_budget_pi {f : ℕ → ℝ} {v : ℝ}
    (hit : ∀ x, SumBudget (leader A p a f x) v) {α : Type*} [Fintype α] (x : α → Site n) :
    SumBudget (fun i : α ↪ ℕ => ∏ l, leader A p a f (x l) (i l)) (v ^ Fintype.card α) := by
  have h := budget_pi _ (fun l => hit (x l))
  simp only [prod_const, card_univ] at h
  exact budget_pull (fun i : α ↪ ℕ => (i : α → ℕ)) DFunLike.coe_injective h

section Marked
variable {V T : Type*} [DecidableEq V] {J : Census V} {o : V → Site n} {p}
variable (H : QuadraticLocal.Hard T p A.forced A.K o J) (w : V → ℝ)

variable {α : Type*} [Fintype α]

/-- Product of outgoing `Poly.price` costs, with the actual compulsory
condition and prescribed hit at *each* of some number of **distinct owners**. This includes quiet terms *and* all
potential marked components. It is a bound before any cancellation,
including of incompatible monomials in the marker algebra. The `u` multiplier
is **only** on the exterior; the output divisor can still be spent once on
a leader term. (`α` empty is also allowed; then no designated hit.) -/
def ownersCharge (t : ℕ → T) (x : α → Site n) (U : Config G n) (i : α ↪ ℕ) (s : Finset ℕ) : ℝ :=
  let f := fun j => Poly.price w (H.hard (t j) j U)
  (∏ l, leader A p a f (x l) (i l)) * restMajorant A p a u f (univ.map i) U s

theorem ownersCharge_nonneg (hu : 0 ≤ u) (hw : ∀ j, 0 < w j) (t : ℕ → T)
    (x : α → Site n) (U : Config G n) (i : α ↪ ℕ) (s : Finset ℕ) : 0 ≤ ownersCharge A a u H w t x U i s :=
  mul_nonneg (prod_nonneg fun l _ => leader_nonneg A p a (fun _ => Poly.nonnegative hw _) (x l) (i l))
    (restMajorant_nonneg A p a u hu (fun _ => Poly.nonnegative hw _) (univ.map i) U s)

theorem ownersCharge_measurable (t : ℕ → T) (x : α → Site n) (i : α ↪ ℕ) (s : Finset ℕ) :
    Measurable fun U => ownersCharge A a u H w t x U i s := by
  have m (j : ℕ) : Measurable (fun U => Poly.price w (H.hard (t j) j U)) :=
    (Poly.price_cont w).measurable.comp (H.locality (t j) j).borel
  unfold ownersCharge leader restMajorant withSupport
  by_cases hi : Disjoint (univ.map i) s
  · simp only [hi, true_and]
    apply Measurable.mul
    · apply Finset.measurable_fun_prod
      intro l _
      by_cases hx : x l ∈ (A.forced (i l)).support
      · simp only [hx, if_true]
        exact (m (i l)).mul_const _
      simp only [hx, if_false]; exact measurable_const
    exact Measurable.ite (A.admissible_borel ..)
      (measurable_fun_prod _ fun j _ => ((m j).mul_const _).const_mul _) measurable_const
  simp only [hi, false_and, if_false, mul_zero]; exact measurable_const

/-- Obtain the header price *before* all independent tests, and bound the
entire roster absolutely by it and a field-dependent companion table. Only
`admissible` in the latter varies (through actual flag reads); no local flag
is dropped in evaluation. -/
theorem ownersCharge_majorant (hw : ∀ j, 0 < w j) {v : ℝ} (paid : H.Paid w p.B a v) :
    ∃ f, (∀ i, 0 ≤ f i) ∧ (∀ x, SumBudget (leader A p a f x) v) ∧
    ∀ u, 0 ≤ u → ∀ (α : Type*) [Fintype α] t (x : α → Site n) U i s,
      ownersCharge A a u H w t x U i s ≤
        (∏ l, leader A p a f (x l) (i l)) * restMajorant A p a u f (univ.map i) U s := by
  obtain ⟨d, dom, hit⟩ := paid.wages
  let f := fun i : ℕ => Poly.price w (d i)
  have nn (i : ℕ) : 0 ≤ f i := Poly.nonnegative hw _
  refine ⟨f, nn, hit, ?_⟩
  intro u hu α _ t x U i s
  let g := fun j => Poly.price w (H.hard (t j) j U)
  have gm (j) : 0 ≤ g j := Poly.nonnegative hw _
  have deflate (j) : withSupport A p a g j ≤ withSupport A p a f j :=
    mul_le_mul_of_nonneg_right ((dom j (t j) U).reprice w hw) (Real.exp_nonneg _)
  have primary (l : α) : leader A p a g (x l) (i l) ≤ leader A p a f (x l) (i l) := by
    unfold leader; split <;> first | exact deflate _ | exact le_rfl
  have rest : restMajorant A p a u g (univ.map i) U s ≤ restMajorant A p a u f (univ.map i) U s := by
    unfold restMajorant; split
    · apply prod_le_prod
      · exact fun j _ => mul_nonneg hu (withSupport_nonneg A p a gm j)
      exact fun j _ => mul_le_mul_of_nonneg_left (deflate j) hu
    exact le_rfl
  exact mul_le_mul (prod_le_prod (fun l _ => leader_nonneg A p a gm (x l) (i l))
    (fun l _ => primary l)) rest (restMajorant_nonneg A p a u hu gm (univ.map i) U s)
    (prod_nonneg fun l _ => leader_nonneg A p a nn (x l) (i l))

/-- Anchored absolute sum of the full marked coefficients including all
admissible exterior labels, uniform in the field. Independent
tests on every occurrence and factor. A product of many factors is evaluated
on the same `U`; this is not a budget in independent fields per global
roster. -/
theorem ownersCharge_budget (hw : ∀ j, 0 < w j) {v : ℝ} (paid : H.Paid w p.B a v)
    (hu : 0 ≤ u) (gate : u*v ≤ 1) (x : α → Site n) (U : Config G n)
    (t : (α ↪ ℕ) × Finset ℕ → ℕ → T) :
    SumBudget (fun z : (α ↪ ℕ) × Finset ℕ => ownersCharge A a u H w (t z) x U z.1 z.2) (v ^ Fintype.card α) := by
  obtain ⟨f, nn, hit, sub⟩ := ownersCharge_majorant A a H w hw paid
  have heads := leader_budget_pi A p a hit x
  refine budget_rows _ _ (h := heads) ?_
  intro i
  have rest := restMajorant_budget A p a u hu nn hit gate (univ.map i) U
  have roof : SumBudget (restMajorant A p a u f (univ.map i) U) 1 :=
    budget_loosen rest (by split <;> first | exact le_rfl | exact gate)
  have bound := budget_mono (budget_scale (heads.1 i) roof)
    (fun s => ownersCharge_nonneg A a u H w hu hw (t (i,s)) x U i s)
    (fun s => sub u hu α (t (i,s)) x U i s)
  rw [mul_one] at bound
  exact bound

end Marked
end YM.Integration.FVA1Physical.QLocalForced1026

