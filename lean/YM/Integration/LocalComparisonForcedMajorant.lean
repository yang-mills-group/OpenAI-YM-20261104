import YM.Integration.LocalComparisonForcedCover

/-!
A common positive polynomial majorant for the full forced numerator.
Its coefficients are chosen before the independent tests, so the supremum
stays inside each weighted coefficient sum.  The original compulsory-cover
condition and all mixed marked products are retained.  Normalized integration
of the exponential background is a separate obligation.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.LocalComparison.ForcedMajorant
open Lattice Wilson RG Marker Finset Overlay RG3.Forms RG3.Script.Picnic
open UniformPolynomialComparison SectorNext.Vacuum Push.AbsoluteSums
open scoped BigOperators Classical

section Algebra
variable {V A X : Type*} [DecidableEq V] {R : Census V}

private lemma positive_send (s : R.Mode) {b : ℝ} (hb : 0 ≤ b) :
    Positive (Poly.send s (b : ℂ)) := by
  intro q
  rw [Poly.part_send]
  split <;> simp [hb]

private lemma dominates_send (s : R.Mode) {f : X → ℂ} {b : ℝ}
    (hf : ∀ x, ‖f x‖ ≤ b) :
    Dominates (Poly.send s (b : ℂ)) (fun x => Poly.send s (f x)) := by
  intro x q
  rw [Poly.part_send, Poly.part_send]
  split
  · exact hf x
  simp

private lemma positive_tsum {f : A → Poly R} (hf : Summable f)
    (hp : ∀ i, Positive (f i)) : Positive (∑' i, f i) := by
  intro q
  have hs : Summable (fun i => (f i).part q) := (Poly.get q).summable hf
  rw [Poly.share hf, Complex.re_tsum hs, Complex.im_tsum hs]
  refine ⟨tsum_nonneg (fun i => (hp i q).1), ?_⟩
  simp only [show ∀ i, ((f i).part q).im = 0 from fun i => (hp i q).2, tsum_zero]

private lemma positive_sum (s : Finset A) (f : A → Poly R)
    (hf : ∀ i ∈ s, Positive (f i)) : Positive (∑ i ∈ s, f i) := by
  intro q
  rw [Poly.part_sum]
  simp only [Complex.re_sum, Complex.im_sum]
  exact ⟨sum_nonneg (fun i hi => (hf i hi q).1),
    sum_eq_zero (fun i hi => (hf i hi q).2)⟩

private lemma dominates_add {a b : Poly R} {f g : X → Poly R}
    (hf : Dominates a f) (hg : Dominates b g) :
    Dominates (a + b) (fun x => f x + g x) := by
  intro x q
  rw [Poly.part_plus, Poly.part_plus, Complex.add_re]
  exact (norm_add_le _ _).trans (add_le_add (hf x q) (hg x q))

private lemma dominates_sum (s : Finset A) {a : A → Poly R} {f : A → X → Poly R}
    (hf : ∀ i ∈ s, Dominates (a i) (f i)) :
    Dominates (∑ i ∈ s, a i) (fun x => ∑ i ∈ s, f i x) := by
  intro x q
  rw [Poly.part_sum, Poly.part_sum, Complex.re_sum]
  exact (norm_sum_le _ _).trans (sum_le_sum (fun i hi => hf i hi x q))

private lemma dominates_tsum {a : A → Poly R} {f : A → X → Poly R}
    (ha : Summable a) (hf : ∀ x, Summable (fun i => f i x))
    (h : ∀ i, Dominates (a i) (f i)) :
    Dominates (∑' i, a i) (fun x => ∑' i, f i x) := by
  intro x q
  have hs : Summable (fun i => (a i).part q |>.re) :=
    Complex.reCLM.summable ((Poly.get q).summable ha)
  have hn : Summable (fun i => ‖(f i x).part q‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => h i x q)
  have hsa : Summable (fun i => (a i).part q) := (Poly.get q).summable ha
  rw [Poly.share (hf x), Poly.share ha, Complex.re_tsum hsa]
  exact (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum (fun i => h i x q) hs)

private lemma positive_prod (s : Finset A) (f : A → Poly R)
    (hf : ∀ i ∈ s, Positive (f i)) : Positive (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa only [prod_empty] using positive_one (J := R)
  | @insert i s hi ih =>
    rw [prod_insert hi]
    exact (hf i (mem_insert_self ..)).mul
      (ih (fun j hj => hf j (mem_insert_of_mem hj)))

private lemma dominates_prod (s : Finset A) {a : A → Poly R}
    {f : A → X → Poly R} (ha : ∀ i ∈ s, Positive (a i))
    (hf : ∀ i ∈ s, Dominates (a i) (f i)) :
    Dominates (∏ i ∈ s, a i) (fun x => ∏ i ∈ s, f i x) := by
  induction s using Finset.induction_on with
  | empty => simpa only [prod_empty] using dominates_one (α := X) (J := R)
  | @insert i s hi ih =>
    simp_rw [prod_insert hi]
    exact (hf i (mem_insert_self ..)).mul
      (ih (fun j hj => ha j (mem_insert_of_mem hj))
        (fun j hj => hf j (mem_insert_of_mem hj)))
      (ha i (mem_insert_self ..))
      (positive_prod s a (fun j hj => ha j (mem_insert_of_mem hj)))

private lemma price_dominated {a : Poly R} {f : X → Poly R}
    (ha : Positive a) (hf : Dominates a f) {w : V → ℝ}
    (hw : ∀ v, 0 < w v) (x : X) : Poly.price w (f x) ≤ Poly.price w a := by
  unfold Poly.price
  apply sum_le_sum
  intro s _
  rw [ha.norm]
  exact mul_le_mul_of_nonneg_left (hf x s) (Poly.worth hw s).le

/-- One distinguished differing factor, with all other marked factors retained. -/
def polyFee (v a : ℕ → Poly R) (s : Finset ℕ) : Poly R :=
  ∑ i ∈ s, a i * ∏ j ∈ s.erase i, v j

lemma polyFee_insert (v a : ℕ → Poly R) {s : Finset ℕ} {i : ℕ} (hi : i ∉ s) :
    polyFee v a (insert i s) = a i * (∏ j ∈ s, v j) + v i * polyFee v a s := by
  unfold polyFee
  rw [sum_insert hi, erase_insert hi, mul_sum]
  congr 1
  apply sum_congr rfl
  intro j hj
  have hji := ne_of_mem_of_not_mem hj hi
  rw [erase_insert_of_ne hji.symm, prod_insert (notMem_mono (erase_subset ..) hi)]
  ring

lemma polyFee_positive (v a : ℕ → Poly R)
    (hv : ∀ i, Positive (v i)) (ha : ∀ i, Positive (a i)) (s : Finset ℕ) :
    Positive (polyFee v a s) :=
  positive_sum s _ (fun i _ => (ha i).mul (positive_prod _ _ (fun j _ => hv j)))

lemma polyFee_price (v a : ℕ → Poly R) (w : V → ℝ) (hw : ∀ i, 0 < w i)
    (b c : ℕ → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hv : ∀ i, Poly.price w (v i) ≤ b i)
    (ha : ∀ i, Poly.price w (a i) ≤ c i) (s : Finset ℕ) :
    Poly.price w (polyFee v a s) ≤ Trace13.Response.fee b c s := by
  unfold polyFee Trace13.Response.fee
  apply (Poly.batch hw _ _).trans
  apply sum_le_sum
  intro i _
  apply (Poly.multiplication hw _ _).trans
  apply mul_le_mul (ha i) _ (Poly.nonnegative hw _) (hc i)
  convert (Poly.multiple hw (s.erase i) v).trans
    (prod_le_prod (s := s.erase i)
      (fun j _ => Poly.nonnegative hw (v j)) (fun j _ => hv j)) using 1
  congr!

/-- Domination is coefficientwise for a whole test population, rather than
only a price estimate made separately for each test. -/
theorem product_difference_dominated
    (v a : ℕ → Poly R) (hv : ∀ i, Positive (v i)) (ha : ∀ i, Positive (a i))
    (f g : ℕ → X → Poly R)
    (hf : ∀ i, Dominates (v i) (f i)) (hg : ∀ i, Dominates (v i) (g i))
    (hd : ∀ i, Dominates (a i) (fun x => f i x - g i x)) (s : Finset ℕ) :
    Dominates (polyFee v a s) (fun x => (∏ i ∈ s, f i x) - ∏ i ∈ s, g i x) := by
  induction s using Finset.induction_on with
  | empty =>
    intro x q
    simp [polyFee, Poly.part_nil]
  | @insert i s hi ih =>
    rw [polyFee_insert v a hi]
    have hF := dominates_prod s (fun j _ => hv j) (fun j _ => hf j)
    have hP := positive_prod s v (fun j _ => hv j)
    have hQ := polyFee_positive v a hv ha s
    have h := dominates_add ((hd i).mul hF (ha i) hP)
      ((hg i).mul ih (hv i) hQ)
    intro x q
    change ‖((∏ j ∈ insert i s, f j x) - ∏ j ∈ insert i s, g j x).part q‖ ≤ _
    rw [prod_insert hi, prod_insert hi]
    rw [show f i x * (∏ j ∈ s, f j x) - g i x * (∏ j ∈ s, g j x) =
      (f i x - g i x) * (∏ j ∈ s, f j x) +
        g i x * ((∏ j ∈ s, f j x) - ∏ j ∈ s, g j x) by ring]
    exact h x q
end Algebra

variable {V : Type} [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} (P : Rep G n)

/-- A test-independent polynomial, with field dependence only through the
original compulsory-cover condition. -/
def cover (v a : ℕ → Poly R) (U : Config G n) : Poly R :=
  ∑' s : Finset ℕ, if P.activities.admissible P.p U s then polyFee v a s else 0

lemma cover_measurable (v a : ℕ → Poly R) : Measurable (cover P v a) := by
  unfold cover
  exact Measurable.tsum (fun s => Measurable.ite
    (P.activities.admissible_borel P.p s) measurable_const measurable_const)

/-- The entire marked packet sum is dominated coefficientwise by one common
positive polynomial. This proof applies the scalar cover estimate only to
that polynomial's price, after fixing its coefficients for all tests. -/
theorem cover_dominates {X : Type*} (F : X → Bands R P)
    (w : V → ℝ) (hw : ∀ z, 0 < w z)
    (v a : ℕ → Poly R) (hv : ∀ i, Positive (v i)) (ha : ∀ i, Positive (a i))
    (b c : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hvPrice : ∀ i, Poly.price w (v i) ≤ b i)
    (haPrice : ∀ i, Poly.price w (a i) ≤ c i)
    {regular vacuum : ℝ} (hP : P.activities.Valid P.p regular vacuum)
    (U : Config G n)
    (hF : ∀ i, Dominates (v i) (fun x => (F x).each i U))
    (hG : ∀ i, Dominates (v i)
      (fun _ : X => Poly.bead R (P.activities.K i U : ℂ)))
    (hD : ∀ i, Dominates (a i) (fun x => (F x).each i U -
      Poly.bead R (P.activities.K i U : ℂ)))
    (γ M : ℝ)
    (hHit : ∀ z : Site n, ∀ I : Finset ℕ,
      (∑ i ∈ I, if z ∈ (P.activities.forced i).inventory then
        b i * Real.exp (γ * (P.activities.forced i).inventory.card) else 0) ≤ 1)
    (hMarked : ∀ I : Finset ℕ,
      (∑ i ∈ I, c i * Real.exp (γ * (P.activities.forced i).inventory.card)) ≤ M) :
    Positive (cover P v a U) ∧
    Dominates (cover P v a U) (fun x => (F x).cluster U -
      Poly.bead R (P.activities.gas P.p U : ℂ)) ∧
    Poly.price w (cover P v a U) ≤ M * Real.exp (-γ * (flags P.p.threshold U).card) := by
  let Q (s : Finset ℕ) : Poly R :=
    if P.activities.admissible P.p U s then polyFee v a s else 0
  let E (s : Finset ℕ) (x : X) : Poly R := (F x).packet s U -
    Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ)
  have hQPositive (s) : Positive (Q s) := by
    unfold Q
    split
    · exact polyFee_positive v a hv ha s
    exact positive_zero
  have hQDom (s) : Dominates (Q s) (E s) := by
    by_cases hs : P.activities.admissible P.p U s
    · unfold Q E Bands.packet Activities.gasOccurrence
      simp only [if_pos hs, Complex.ofReal_prod, map_prod]
      exact product_difference_dominated v a hv ha
        (fun i x => (F x).each i U)
        (fun i (_ : X) => Poly.bead R (P.activities.K i U : ℂ)) hF hG hD s
    intro x q
    simp [Q, E, Bands.packet, Activities.gasOccurrence, hs]
  have hQCost : SumBudget (fun s => Poly.price w (Q s))
      (M * Real.exp (-γ * (flags P.p.threshold U).card)) := by
    apply budget_of_sum (fun s => Poly.nonnegative hw _)
    intro S
    let I := S.biUnion id
    let A := S.filter (P.activities.admissible P.p U)
    have hSubset : A ⊆ I.powerset.filter
        (accounted (fun i => (P.activities.forced i).support)
          (fun i => (P.activities.forced i).inventory) (flags P.p.threshold U)) := by
      intro s hs
      obtain ⟨hsS, hs⟩ := mem_filter.mp hs
      have he : P.activities.admissible P.p U s =
          accounted (fun i => (P.activities.forced i).support)
            (fun i => (P.activities.forced i).inventory) (flags P.p.threshold U) s := by
        unfold Activities.admissible accounted
        congr!
      exact mem_filter.mpr ⟨mem_powerset.mpr
        (fun i hi => mem_biUnion.mpr ⟨s, hsS, hi⟩), he ▸ hs⟩
    calc
      _ = ∑ s ∈ A, Poly.price w (Q s) := by
        symm
        apply sum_subset (filter_subset ..)
        intro s hs hNot
        have h : ¬P.activities.admissible P.p U s :=
          fun h => hNot (mem_filter.mpr ⟨hs, h⟩)
        simp [Q, h]
      _ ≤ ∑ s ∈ A, Trace13.Response.fee b c s := by
        apply sum_le_sum
        intro s hs
        simp only [Q, if_pos (mem_filter.mp hs).2]
        exact polyFee_price v a w hw b c hc hvPrice haPrice s
      _ ≤ ∑ s ∈ I.powerset.filter
          (accounted (fun i => (P.activities.forced i).support)
            (fun i => (P.activities.forced i).inventory) (flags P.p.threshold U)),
          Trace13.Response.fee b c s :=
        sum_le_sum_of_subset_of_nonneg hSubset
          (fun s _ _ => sum_nonneg
            (fun i _ => mul_nonneg (hc i) (prod_nonneg (fun j _ => hb j))))
      _ ≤ _ := ForcedCover.marked_cover
        (fun i => (P.activities.forced i).support)
        (fun i => (P.activities.forced i).inventory)
        (fun i => (P.activities.forced i).inventory_sup)
        (fun i => (P.activities.forced i).inventory_ne)
        b c hb hc γ M (fun z I => by convert hHit z I using 1; congr!)
        hMarked (flags P.p.threshold U) I
  have hQ := Poly.budgeted hw hQCost.2.1 (fun _ => le_rfl)
  have hE (x : X) : Summable (fun s => E s x) :=
    (Poly.budgeted hw hQCost.2.1
      (fun s => price_dominated (hQPositive s) (hQDom s) hw x)).1
  have hGas : Summable (fun s : Finset ℕ =>
      Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ)) := by
    apply (Poly.budgeted hw ((Activities.gasSeries hP).absolute U) ?_).1
    intro s
    change Poly.price w (Poly.send R.quiet
      (P.activities.gasOccurrence P.p s U : ℂ)) ≤ _
    rw [Poly.solo, Poly.quiet_toll, one_mul, Complex.norm_real]
  have hGasSum : (∑' s : Finset ℕ,
      Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ)) =
      Poly.bead R (P.activities.gas P.p U : ℂ) := by
    change (∑' s : Finset ℕ, Poly.send R.quiet
      (P.activities.gasOccurrence P.p s U : ℂ)) =
      Poly.send R.quiet (P.activities.gas P.p U : ℂ)
    have hSend : Summable (fun s : Finset ℕ => Poly.send R.quiet
        (P.activities.gasOccurrence P.p s U : ℂ)) := hGas
    ext j
    rw [Poly.share hSend]
    by_cases hj : j = R.quiet
    · subst j
      simp only [Poly.part_send, ite_true, Activities.gas, Complex.ofReal_tsum]
    simp only [Poly.part_send, if_neg hj, tsum_zero]
  have hESum (x : X) : (∑' s, E s x) =
      (F x).cluster U - Poly.bead R (P.activities.gas P.p U : ℂ) := by
    have hBands : Summable (fun s => (F x).packet s U) := by
      simpa only [E, sub_add_cancel] using (hE x).add hGas
    rw [show (∑' s, E s x) = (∑' s, (F x).packet s U) -
      ∑' s, Poly.bead R (P.activities.gasOccurrence P.p s U : ℂ) from
        hBands.tsum_sub hGas]
    rw [hGasSum]
    rfl
  refine ⟨positive_tsum hQ.1 hQPositive, ?_, hQ.2.trans hQCost.2.2⟩
  intro x q
  change ‖((F x).cluster U - Poly.bead R (P.activities.gas P.p U : ℂ)).part q‖ ≤ _
  rw [← hESum x]
  exact dominates_tsum hQ.1 hE hQDom x q

lemma cover_zero (v a : ℕ → Poly R) (U : Config G n)
    (hFlags : flags P.p.threshold U = ∅) : cover P v a U = 0 := by
  unfold cover
  suffices hz : ∀ s : Finset ℕ,
      (if P.activities.admissible P.p U s then polyFee v a s else 0) = (0 : Poly R) by
    simp only [hz, tsum_zero]
  intro s
  by_cases hs : s = ∅
  · subst s
    simp [polyFee]
  have hNot : ¬P.activities.admissible P.p U s := by
    intro h
    obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.mpr hs
    obtain ⟨y, hy⟩ := (P.activities.forced i).inventory_ne
    have hyFlags : y ∈ flags P.p.threshold U :=
      h.2 ▸ mem_biUnion.mpr ⟨i, hi, hy⟩
    simp only [hFlags, notMem_empty] at hyFlags
  simp [hNot]

end YM.Integration.LocalComparison.ForcedMajorant

namespace YM.Integration.LocalComparison
open Lattice Wilson RG Marker Finset Overlay RG3.Forms RG3.Script.Picnic
open UniformPolynomialComparison SectorNext.Vacuum Push.AbsoluteSums ForcedMajorant
open scoped BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
    {G : Gauge} {n : Side} {P : Rep G n} {X : Type*}
    {o : V → Site n} {T : Taste X o P R} {p : BudgetPoint}
    {w : V → ℝ} {κ regularPrice forcedPrice : ℝ}

/-- One measurable positive polynomial field dominates the full forced
numerator for every independent test simultaneously. The same support
reserve and marked hit budget pay its price; there is no mode-count loss. -/
theorem FullBudget.forced_majorant
    (h : FullBudget p T w κ regularPrice forcedPrice) (x₀ : X)
    {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1) :
    ∃ Q : Config G n → Poly R, Measurable Q ∧ ∀ U,
      Positive (Q U) ∧
      Dominates (Q U) (fun x : X => forcedClusterError (T.leaf x) U) ∧
      Poly.price w (Q U) ≤
        if flags P.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
            Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  let M := (Fintype.card V : ℝ) * (κ * forcedPrice)
  let γ := flagRate p
  let Z (i : ℕ) := (P.activities.forced i).inventory
  let q (ij : ℕ × ℕ) := Poly.toll w (T.menu.marks ij.1 ij.2) *
    p.mass (P.activities.forced ij.1).support (h.black ij)
  have hqNonnegative (ij) : 0 ≤ q ij :=
    mul_nonneg (Poly.worth h.radii _).le
      ((h.black_nonnegative ij).trans (p.loMass _ _ (h.black_nonnegative ij)))
  have hq : SumBudget q M := Overlay.per_system hqNonnegative
    (fun ij => (h.active x₀).articles.occurs ij.1 ij.2) h.forcedTotal
  obtain ⟨hFiber, hOuter⟩ :=
    (summable_prod_of_nonneg (show 0 ≤ q from hqNonnegative)).mp hq.2.1
  let b (i : ℕ) := ∑' j, q (i, j)
  let c (i : ℕ) := Real.exp (-γ * (Z i).card) * b i
  let a (i : ℕ) : Poly R :=
    ∑' j, Poly.send (T.menu.marks i j) (h.black (i, j) : ℂ)
  have hb (i) : 0 ≤ b i := tsum_nonneg (fun j => hqNonnegative (i, j))
  have hc (i) : 0 ≤ c i := mul_nonneg (Real.exp_pos _).le (hb i)
  have hRestore (i) : c i * Real.exp (γ * (Z i).card) = b i := by
    change (Real.exp (-γ * (Z i).card) * b i) * Real.exp (γ * (Z i).card) = b i
    calc
      _ = (Real.exp (-γ * (Z i).card) * Real.exp (γ * (Z i).card)) * b i := by ring
      _ = _ := by rw [← Real.exp_add]; simp
  have hMarked (I : Finset ℕ) :
      (∑ i ∈ I, c i * Real.exp (γ * (Z i).card)) ≤ M := by
    simp_rw [hRestore]
    exact (hOuter.sum_le_tsum I (fun i _ => hb i)).trans
      ((hq.2.1.tsum_prod).symm.trans_le hq.2.2)
  have hInventory (i) : γ * (Z i).card ≤
      p.supportExponent * coverNumber p.B (P.activities.forced i).support :=
    inventory_pay p (P.activities.forced i).inventory_sup
  have hCompensate (i) : 1 ≤ Real.exp (-γ * (Z i).card) *
      Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    linarith only [hInventory i]
  have hTerm (i j : ℕ) :
      Poly.price w (Poly.send (T.menu.marks i j) (h.black (i, j) : ℂ)) ≤
        Real.exp (-γ * (Z i).card) * q (i, j) := by
    rw [Poly.solo, Complex.norm_real, Real.norm_of_nonneg (h.black_nonnegative _)]
    calc
      _ = 1 * (Poly.toll w (T.menu.marks i j) * h.black (i, j)) := by ring
      _ ≤ (Real.exp (-γ * (Z i).card) * Real.exp
          (p.supportExponent * coverNumber p.B (P.activities.forced i).support)) *
          (Poly.toll w (T.menu.marks i j) * h.black (i, j)) :=
        mul_le_mul_of_nonneg_right (hCompensate i)
          (mul_nonneg (Poly.worth h.radii _).le (h.black_nonnegative _))
      _ = _ := by unfold q BudgetPoint.mass; ring
  have hASum (i) : Summable
      (fun j => Poly.send (T.menu.marks i j) (h.black (i, j) : ℂ)) :=
    (Poly.budgeted h.radii ((hFiber i).mul_left (Real.exp (-γ * (Z i).card)))
      (hTerm i)).1
  have hAPrice (i) : Poly.price w (a i) ≤ c i := by
    exact (Poly.budgeted h.radii ((hFiber i).mul_left (Real.exp (-γ * (Z i).card)))
      (hTerm i)).2.trans_eq (by rw [tsum_mul_left])
  have hAPositive (i) : Positive (a i) :=
    positive_tsum (hASum i) (fun j => positive_send _ (h.black_nonnegative (i, j)))
  have hActualTerm (U : Config G n) (i j) (x : X) :
      Poly.price w ((T.leaf x).contents.tagged i j U) ≤
        Real.exp (-γ * (Z i).card) * q (i, j) := by
    apply le_trans _ (hTerm i j)
    change Poly.price w (Poly.send (T.menu.marks i j) (T.menu.force x i j U)) ≤ _
    rw [Poly.solo, Poly.solo, Complex.norm_real,
      Real.norm_of_nonneg (h.black_nonnegative _)]
    exact mul_le_mul_of_nonneg_left (h.forced x i j U) (Poly.worth h.radii _).le
  have hActualSum (U : Config G n) (i) (x : X) :
      Summable (fun j => (T.leaf x).contents.tagged i j U) :=
    (Poly.budgeted h.radii ((hFiber i).mul_left (Real.exp (-γ * (Z i).card)))
      (fun j => hActualTerm U i j x)).1
  have hADom (U : Config G n) (i) : Dominates (a i)
      (fun x : X => ∑' j, (T.leaf x).contents.tagged i j U) := by
    apply dominates_tsum (hASum i) (hActualSum U i)
    intro j
    exact dominates_send _ (fun x => h.forced x i j U)
  obtain ⟨k, hk, hK⟩ := hReserve
  let v (i : ℕ) : Poly R := Poly.bead R (k i : ℂ) + a i
  have hVPositive (i) : Positive (v i) :=
    (positive_send R.quiet (hk i).1).add (hAPositive i)
  have hVPrice (i) : Poly.price w (v i) ≤ k i + c i := by
    apply (Poly.addition h.radii _ _).trans
    apply add_le_add _ (hAPrice i)
    simp [Poly.bead, Poly.solo, Poly.quiet_toll, Complex.norm_real,
      Real.norm_of_nonneg (hk i).1]
  have hBaseHit (z : Site n) (I : Finset ℕ) :
      (∑ i ∈ I, if z ∈ Z i then k i * Real.exp (γ * (Z i).card) else 0) ≤ vacuum := by
    apply le_trans _ (budget_sum (hK z) I)
    apply sum_le_sum
    intro i _
    split_ifs with hZ hSupport
    · unfold BudgetPoint.mass
      rw [mul_comm (k i)]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hInventory i)) (hk i).1
    · exact False.elim (hSupport ((P.activities.forced i).inventory_sup hZ))
    · exact (hk i).1.trans (p.loMass _ _ (hk i).1)
    exact le_rfl
  have hHit (z : Site n) (I : Finset ℕ) :
      (∑ i ∈ I, if z ∈ Z i then
        (k i + c i) * Real.exp (γ * (Z i).card) else 0) ≤ 1 := by
    calc
      _ ≤ (∑ i ∈ I, if z ∈ Z i then k i * Real.exp (γ * (Z i).card) else 0) +
          ∑ i ∈ I, c i * Real.exp (γ * (Z i).card) := by
        rw [← sum_add_distrib]
        apply sum_le_sum
        intro i _
        split_ifs
        · exact (add_mul ..).le
        exact le_add_of_nonneg_right (mul_nonneg (hc i) (Real.exp_pos _).le)
      _ ≤ vacuum + M := add_le_add (hBaseHit z I) (hMarked I)
      _ ≤ 1 := hSmall
  refine ⟨cover P v a, cover_measurable P v a, fun U => ?_⟩
  have hBaseDom (i) : Dominates (Poly.bead R (k i : ℂ))
      (fun _ : X => Poly.bead R (P.activities.K i U : ℂ)) :=
    dominates_send R.quiet (fun _ => by simpa only [Complex.norm_real] using (hk i).2 U)
  have hFDom (i) : Dominates (v i) (fun x : X => (T.leaf x).contents.each i U) :=
    dominates_add (hBaseDom i) (hADom U i)
  have hGDom (i) : Dominates (v i)
      (fun _ : X => Poly.bead R (P.activities.K i U : ℂ)) := by
    intro x q
    apply (hBaseDom i x q).trans
    change ((Poly.bead R (k i : ℂ)).part q).re ≤
      ((Poly.bead R (k i : ℂ) + a i).part q).re
    rw [Poly.part_plus, Complex.add_re]
    exact le_add_of_nonneg_right (hAPositive i q).1
  have hDDom (i) : Dominates (a i) (fun x : X =>
      (T.leaf x).contents.each i U - Poly.bead R (P.activities.K i U : ℂ)) := by
    intro x q
    change ‖((Poly.bead R (P.activities.K i U : ℂ) +
      ∑' j, (T.leaf x).contents.tagged i j U) -
        Poly.bead R (P.activities.K i U : ℂ)).part q‖ ≤ _
    rw [add_sub_cancel_left]
    exact hADom U i x q
  obtain ⟨hPos, hDom, hPrice⟩ := cover_dominates P
    (fun x : X => (T.leaf x).contents) w h.radii v a hVPositive hAPositive
    (fun i => k i + c i) c (fun i => add_nonneg (hk i).1 (hc i)) hc
    hVPrice hAPrice hP U hFDom hGDom hDDom γ M hHit hMarked
  refine ⟨hPos, ?_, ?_⟩
  · have hBead (z : ℂ) : Poly.bead R z = z • (1 : Poly R) := by
      simpa only [mul_one] using Poly.product_bead (1 : Poly R) z
    simpa only [forcedClusterError, hBead] using hDom
  split_ifs with hFlags
  · rw [cover_zero P v a U hFlags, Poly.zero_price]
  exact hPrice

/-- The test supremum is inside each weighted coefficient sum. -/
theorem FullBudget.forced_uniform_price
    (h : FullBudget p T w κ regularPrice forcedPrice) (x₀ : X)
    {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (U : Config G n) :
    uniformPrice w (fun x : X => forcedClusterError (T.leaf x) U) ≤
      if flags P.p.threshold U = ∅ then 0 else
        ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
          Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  obtain ⟨Q, _, hQ⟩ := h.forced_majorant x₀ hP hReserve hSmall
  exact (uniformPrice_le (hQ U).1 (hQ U).2.1 h.radii).trans (hQ U).2.2

omit [Fintype V] in
private theorem forced_restored_positive (cost : R.Mode → ℝ)
    (hcost : ∀ s, 0 < cost s) {A : Poly R} (hA : Positive A) :
    Positive (restoreEnvelope cost hcost A) := by
  intro s
  change 0 ≤ ((cost s : ℂ) * A.part s).re ∧ ((cost s : ℂ) * A.part s).im = 0
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  exact ⟨mul_nonneg (hcost s).le (hA s).1, by rw [(hA s).2, mul_zero]⟩

/-- The common polynomial is restored to the original physical coefficients,
with every product kernel envelope retained. Its field dependence remains
measurable and independent of all test choices. -/
theorem RelativeBudget.physical_forced_majorant {cost : V → ℝ}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (x₀ : X)
    {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1) :
    ∃ Q : Config G n → Poly R, Measurable Q ∧ ∀ U,
      Positive (Q U) ∧
      Dominates (Q U) (fun x : X => forcedClusterError (T.leaf x) U) ∧
      Poly.price (fun v => w v / cost v) (Q U) ≤
        if flags P.p.threshold U = ∅ then 0 else
          ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
            Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  obtain ⟨Q, hMeas, hQ⟩ := h.budget.forced_majorant x₀ hP hReserve hSmall
  let E : Poly R ≃L[ℂ] Poly R :=
    restoreEnvelope (envelopeProduct cost) (envelopeProduct_positive hcost)
  refine ⟨fun U => E (Q U), E.continuous.measurable.comp hMeas, fun U => ?_⟩
  refine ⟨forced_restored_positive _ _ (hQ U).1, ?_, ?_⟩
  · intro x s
    have he := congrArg (fun A : Poly R => A.part s)
      (restoreEnvelope_forcedClusterError T cost hcost x U)
    change (envelopeProduct cost s : ℂ) * _ = _ at he
    change ‖(forcedClusterError (T.leaf x) U).part s‖ ≤
      ((envelopeProduct cost s : ℂ) * (Q U).part s).re
    rw [← he, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (envelopeProduct_positive hcost s).le]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_left ((hQ U).2.1 x s)
      (envelopeProduct_positive hcost s).le
  exact (restoreEnvelope_product_price cost w hcost _).trans_le (hQ U).2.2

/-- Full forced uniformity for the original physical coefficients. -/
theorem RelativeBudget.physical_forced_uniform_price {cost : V → ℝ}
    (h : RelativeBudget p T w κ (envelopeProduct cost) regularPrice forcedPrice)
    (hcost : ∀ v, 0 < cost v) (x₀ : X)
    {regular actualVacuum vacuum : ℝ}
    (hP : P.activities.Valid P.p regular actualVacuum)
    (hReserve : P.activities.KBound p vacuum)
    (hSmall : vacuum + (Fintype.card V : ℝ) * (κ * forcedPrice) ≤ 1)
    (U : Config G n) :
    uniformPrice (fun v => w v / cost v)
      (fun x : X => forcedClusterError (T.leaf x) U) ≤
      if flags P.p.threshold U = ∅ then 0 else
        ((Fintype.card V : ℝ) * (κ * forcedPrice)) *
          Real.exp (-flagRate p * (flags P.p.threshold U).card) := by
  obtain ⟨Q, _, hQ⟩ := h.physical_forced_majorant hcost x₀ hP hReserve hSmall
  exact (uniformPrice_le (hQ U).1 (hQ U).2.1
    (fun v => div_pos (h.budget.radii v) (hcost v))).trans (hQ U).2.2

end YM.Integration.LocalComparison
