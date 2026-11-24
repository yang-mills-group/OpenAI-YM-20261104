import YM.Integration.WilsonCenteredNestedProducts

/-! Engineering normalization for every leaf in the original finite nesting.
A leaf is charged at its immediate parent's radius. Each actual intermediate
grade, including grade zero, is transported by its own nonnegative power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedRates
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite
open Extraction Spec Table
open scoped Classical BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def leaves : (t : Tree) → (t.Inner → ℝ) → (t.Leaf → ℕ) → ℝ → ℝ
  | bud,_,d,a => (a^(d ()))⁻¹
  | fork _ p,s,d,_ => ∏ i,leaves (p i) (childAge i s) (childWages i d) (s (.inl ()))

theorem leaves_nonnegative (t : Tree) (s : t.Inner → ℝ) (d : t.Leaf → ℕ)
    {a : ℝ} (ha : 0 < a) (tar : t.Tapered a 1 s) : 0 ≤ leaves t s d a := by
  induction t generalizing a with
  | bud => exact inv_nonneg.mpr (pow_nonneg ha.le _)
  | fork n p ih => exact Finset.prod_nonneg (fun i _=>
      ih i _ _ tar.1 (by simpa only [mul_one] using tar.2.2 i))

def premium : (t : Tree) → (t.Inner → ℕ) → (t.Inner → ℝ) → (ℝ → ℝ) → ℝ
  | bud,_,_,_ => 1
  | fork _ p,D,s,A =>
      (Fintype.card (Branches F Q (f:=p) (rollCaps D)) : ℝ) *
      ((∏ i,premium (p i) (childAge i D) (childAge i s) A) * A (s (.inl ())))

theorem premium_nonnegative (t : Tree) (D : t.Inner → ℕ) (s : t.Inner → ℝ)
    (A : ℝ → ℝ) (nn : ∀ r,0 ≤ A r) : 0 ≤ premium F Q t D s A := by
  induction t with
  | bud => exact zero_le_one
  | fork n p ih =>
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Finset.prod_nonneg
      (fun i _=>ih i _ _)) (nn _))

/-- The fixed branching count and the product of actual, distinct local
logarithmic prices. No change of coupling along a long edge. -/
theorem separated (t : Tree) (D : t.Inner → ℕ) (s : t.Inner → ℝ) (A : ℝ → ℝ) :
    premium F Q t D s A = premium F Q t D s (fun _=>1) * ∏ v:t.Inner,A (s v) := by
  induction t with
  | bud => simp [premium,Tree.Inner]
  | fork n p ih =>
    rw [prod_inner]
    simp only [premium,mul_one]
    simp_rw [ih]
    rw [Finset.prod_mul_distrib]
    dsimp only [childAge]; ring

theorem cancel {n : ℕ} (r : ℝ) (rp : 0 < r) (e : Fin n → ℕ)
    (a b : Fin n → ℝ) (m : ℕ) (A : ℝ) :
    (∏ i,(a i * r^(e i)) * b i) * (A * (r^m / ∏ i,r^(e i))) =
      (((∏ i,a i) * A) * r^m) * ∏ i,b i := by
  have ne : (∏ i,r^(e i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ rp.ne')
  simp only [Finset.prod_mul_distrib]
  field_simp


end YM.Integration.WilsonCenteredNestedRates
