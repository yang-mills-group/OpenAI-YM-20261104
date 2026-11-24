import YM.RG03.Attach.Ring
import YM.Marker.Truncated

/-! # Exact gas and logarithmic factor identities

Use `Marker.Poly R` at one common census, so exclusions kill products *in the ring*
before taking the mask comparison, never differentiate a conditional probability
with an independently chosen singleton vacuum. (We aren't asserting here that a
reduced marker computation determines any omitted coefficient.) -/

set_option autoImplicit false
noncomputable section
namespace YM.RG03.Gather
open Lattice Wilson RG Function Filter MeasureTheory Finset Marker Pert.Attach
open scoped Topology BigOperators Classical
variable {V : Type*} [DecidableEq V] {R : Census V}
    {n : Side} {G : Gauge} {A : Activities G n} {X : Corrections G n} {P : BudgetPoint}
    {U : Config G n} {r : V → ℝ}

variable (A)
def gasAt (P : BudgetPoint) (K : ℕ → Poly R) (U : Config G n) (s : Finset ℕ) : Poly R :=
  if A.admissible P U s then ∏ i∈s, K i else 0

def poem (P : BudgetPoint) (K : ℕ → Config G n → Poly R) (U : Config G n) := ∑' s, gasAt A P (fun i=> K i U) U s
variable {A}

lemma purchases {α : Type*} {K : α → Poly R} (hr : ∀ i, 0<r i) (h : Summable (fun i => Poly.price r (K i))) :
    Summable (fun s : Finset α => Poly.price r (∏ i∈s, K i)) :=
  (summable_finsetProd_of_summable_nonneg (fun i=>Poly.nonnegative hr (K i)) h).of_nonneg_of_le
    (fun _=> Poly.nonnegative hr _) (fun _ => Poly.multiple hr _ _)

lemma gas_series {K : ℕ → Poly R} (hr : ∀ i,0<r i) (hi : Summable fun i=> Poly.price r (K i)) :
    Summable (fun s : Finset ℕ=> gasAt A P K U s) := by
  refine (Poly.budgeted hr (purchases hr hi) (fun i=>?_)).1
  unfold gasAt; split; exact le_rfl
  rw [Poly.zero_price]; exact Poly.nonnegative hr _

local instance : IsTopologicalSemiring (Poly R) where

lemma at_split {s : Finset Old} {K J : ℕ → Poly R} :
    initial A U P (Sum.elim K J) s = gasAt A P K U s.toLeft * ∏ i∈s.toRight,J i := by
  unfold initial gasAt; split
  · exact prod_sum_eq_prod_toLeft_mul_prod_toRight s (Sum.elim K J)
  rw [zero_mul]

/- Absolute convergence follows from summable input price weights at this configuration.
No statement about conditional normalization is used. -/
lemma start_limit {K J : ℕ → Poly R} (hr : ∀ i,0<r i)
    (hi : Summable fun i=> Poly.price r (K i)) (hj : Summable fun i=> Poly.price r (J i)) :
    HasSum (initial A U P (Sum.elim K J))
      ((∑' s : Finset ℕ,gasAt A P K U s) * ∏' i,(1+J i)) := by
  let W:= Sum.elim K J
  have hs : Summable (fun i => Poly.price r (W i)) := Summable.sum _ hi hj
  have he : Summable (initial A U P W) := by
    refine (Poly.budgeted hr (purchases hr hs) (fun i=>?_)).1
    unfold initial; split; rfl
    rw [Poly.zero_price]; exact Poly.nonnegative hr _
  have ha: Summable fun s : Finset ℕ => ∏ i∈s,J i := (Poly.budgeted hr (purchases hr hj) (fun _=>le_rfl)).1
  let e := (@Finset.sumEquiv ℕ ℕ).toEquiv
  rw [← e.symm.hasSum_iff, tprod_one_add ha]
  have hi' (p : Finset ℕ × Finset ℕ) : initial A U P W (e.symm p) = gasAt A P K U p.1 * ∏ i∈p.2,J i := by
    unfold W; rw [at_split, show (e.symm p).toLeft = p.1 from congrArg Prod.fst (e.apply_symm_apply p),
      show (e.symm p).toRight = p.2 from congrArg Prod.snd (e.apply_symm_apply p)]
  have hx := e.symm.summable_iff.mpr he
  have hGas : Summable (gasAt A P K U) := gas_series hr hi
  change HasSum (initial A U P W ∘ e.symm) ((∑' s,gasAt A P K U s) * ∑' s: Finset ℕ,∏ i∈s,J i)
  simp_rw [comp_def,hi'] at hx ⊢
  convert hx.hasSum using 1
  rw [hx.tsum_prod]
  have h1 (g : Poly R) := (ha.hasSum.mul_left g).tsum_eq
  simp_rw [h1]
  exact (hGas.hasSum.mul_right _).tsum_eq.symm

theorem merged {K J : ℕ → Poly R}
    (hK : ∀ j, K j ≠ 0 → (A.forced j).eligible P.threshold U)
    (hX : ∀ j, Healthy P.threshold (X.region j) U → J j=0)
    (hr : ∀ i,0<r i) (hi : Summable fun i=> Poly.price r (K i)) (hj : Summable fun i=> Poly.price r (J i)) :
    HasSum (outWord A X U P (Sum.elim K J)) ((∑' s,gasAt A P K U s) * ∏' i,(1+J i)) :=
  (reindexed (W:=Sum.elim K J) hK hX _).2 (start_limit hr hi hj)
end YM.RG03.Gather
