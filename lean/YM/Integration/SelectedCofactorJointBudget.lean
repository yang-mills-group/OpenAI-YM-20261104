import YM.Integration.SelectedCofactorSupportBudget

/-! Uniform support-weighted prices for all actual packet cofactors before the
single vacuum exponential. All correlations and marked partners stay in the terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorJointBudget
open Function Finset MeasureTheory Lattice Wilson RG Marker Overlay
open LocalComparison RG3.Forms RG3.Script.Picnic Push.AbsoluteSums
open NativeTasteCoveredCofactor CoveredSignedCofactors SelectedCofactorSupportBudget
open scoped Classical BigOperators Topology

private theorem pair_budget {I J : Type*} {f : I → J → ℝ} {a : I → ℝ} {c : ℝ}
    (ha : SumBudget a c) (hf : ∀ i, SumBudget (f i) (a i)) :
    SumBudget (fun p : I × J => f p.1 p.2) c := by
  refine budget_of_sum (fun p => (hf p.1).1 p.2) fun s => ?_
  let A := s.image Prod.fst
  let B := s.image Prod.snd
  have hs : s ⊆ A ×ˢ B := fun p hp => mem_product.mpr ⟨mem_image_of_mem _ hp,mem_image_of_mem _ hp⟩
  calc
    _ ≤ ∑ p ∈ A ×ˢ B, f p.1 p.2 := sum_le_sum_of_subset_of_nonneg hs fun p _ _ => (hf p.1).1 p.2
    _ = ∑ i ∈ A, ∑ j ∈ B, f i j := sum_product ..
    _ ≤ c := (sum_le_sum fun i _ => budget_sum (hf i) B).trans (budget_sum ha A)

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    {G : Gauge} {n : Side} {X : Type*} {P : Rep G n} {o : V → Site n}
    {T : Taste X o P R} {p pK : BudgetPoint} {w cost : V → ℝ}
    {κ reg fro vacuum : ℝ}

/-- Ordered signed physical row attached to its full admissible minor. -/
def term (D : Deck R P) (U : Config G n) (a : ℕ × Finset ℕ) : Poly R :=
  (D.contents.each a.1 U - scalarRow P U a.1) * cofactor D U a.1 a.2

/-- All-mode support-weighted joint price, independent of field and volume.
The total is charged to a fixed number of marker slots. -/
theorem support_price (h : RelativeBudget p T w κ (envelopeProduct cost) reg fro) (hc : ∀v, 0 < cost v)
    (hK : P.activities.KBound pK vacuum) (hs : vacuum + Fintype.card V * (κ * fro) ≤ 1)
    (x : X) (U : Config G n) :
    SumBudget (fun a : ℕ × Finset ℕ => p.mass (P.activities.forced a.1).support
      (Poly.price (fun v => w v / cost v) (term (T.leaf x) U a))) (Fintype.card V * (κ * fro)) := by
  obtain ⟨m,k,hm,_,hMass,hHit,hRows⟩ := rows h hc hK x
  let w' := fun v => w v / cost v
  have hw v : 0 < w' v := div_pos (h.budget.radii v) (hc v)
  have hcf (i) : SumBudget (fun s => Poly.price w' (cofactor (T.leaf x) U i s)) 1 :=
    CoveredSignedSeries.cofactor_budget hw (fun i => (P.activities.forced i).support)
      (fun i => (P.activities.forced i).inventory) (fun i => (P.activities.forced i).inventory_sup)
      (fun i => (P.activities.forced i).inventory_ne) hs
      (fun i => (T.leaf x).contents.each i U) (scalarRow P U) (fun i => k i + m i)
      (fun i => (hRows x U i).2.1) (fun i => (hRows x U i).2.2.trans (le_add_of_nonneg_right (hm i)))
      hHit (flags P.p.threshold U) i
  apply pair_budget (f := fun i (s : Finset ℕ) => p.mass (P.activities.forced i).support
    (Poly.price w' (term (T.leaf x) U (i,s)))) hMass
  intro i
  let u := p.mass (P.activities.forced i).support (m i)
  have H := budget_scale (show 0 ≤ u from hMass.1 i) (hcf i)
  rw [mul_one] at H
  apply budget_mono H
  · intro s
    exact mul_nonneg (Real.exp_pos _).le (Poly.nonnegative hw _)
  intro s
  let e := Real.exp (p.supportExponent * coverNumber p.B (P.activities.forced i).support)
  change e * Poly.price w' (( (T.leaf x).contents.each i U - scalarRow P U i) * cofactor (T.leaf x) U i s) ≤
    (e*m i) * Poly.price w' (cofactor (T.leaf x) U i s)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left ((Poly.multiplication hw _ _).trans
    (mul_le_mul_of_nonneg_right (hRows x U i).1 (Poly.nonnegative hw _))) (Real.exp_pos _).le

/-- Only the distinguished support enters the geometric cutoff. Arbitrary additional
row, ancestor or reflected labels can remain in the selector. -/
theorem group_price (h : RelativeBudget p T w κ (envelopeProduct cost) reg fro) (hc : ∀v, 0 < cost v)
    (hK : P.activities.KBound pK vacuum) (hs : vacuum + Fintype.card V * (κ * fro) ≤ 1)
    (x : X) (U : Config G n) (Q : (ℕ × Finset ℕ) → Prop) (s : ℕ)
    (hQ : ∀ a, Q a → s ≤ coverNumber p.B (P.activities.forced a.1).support) :
    Summable (fun a : {a // Q a} => term (T.leaf x) U a.val) ∧
      Poly.price (fun v => w v / cost v) (∑' a : {a // Q a}, term (T.leaf x) U a.val) ≤
        Real.exp (-(p.supportExponent * s)) * (Fintype.card V * (κ * fro)) := by
  let w' := fun v => w v / cost v
  have hw v : 0 < w' v := div_pos (h.budget.radii v) (hc v)
  let k := Real.exp (-(p.supportExponent * s))
  have hz : 0 ≤ k := (Real.exp_pos _).le
  have H := budget_scale hz (budget_pull (fun a : {a // Q a} => a.val) Subtype.val_injective (support_price h hc hK hs x U))
  have hp (a : {a // Q a}) : Poly.price w' (term (T.leaf x) U a.val) ≤
      k * p.mass (P.activities.forced a.val.1).support (Poly.price w' (term (T.leaf x) U a.val)) := by
    let v := Poly.price w' (term (T.leaf x) U a.val)
    let d := p.supportExponent * coverNumber p.B (P.activities.forced a.val.1).support
    change v ≤ k * (Real.exp d * v)
    rw [← mul_assoc]
    apply le_mul_of_one_le_left (Poly.nonnegative hw _)
    rw [show k * Real.exp d = Real.exp (-(p.supportExponent * (s:ℝ)) + d) from (Real.exp_add ..).symm]
    apply Real.one_le_exp
    dsimp only [d]
    linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hQ a.val a.property) : (s:ℝ) ≤ _) p.exponent_pos.le]
  have H' := budget_mono H (fun a => Poly.nonnegative hw (term (T.leaf x) U a.val)) hp
  have hg := Poly.budgeted hw H'.2.1 (fun a : {a // Q a} => le_refl (Poly.price w' (term (T.leaf x) U a.val)))
  exact ⟨hg.1,hg.2.trans H'.2.2⟩

end YM.Integration.SelectedCofactorJointBudget
end
