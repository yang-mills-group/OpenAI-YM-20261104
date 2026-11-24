import YM.Integration.FVA1Physical.Marked.MixedBudget
import YM.Push.LOCAL_SPLITTING.Budget

/-! For mixed failed sources, charge each group to its own actual host.
The native support weight is charged only for the sources touching that host.
Different groups can be arbitrarily far apart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Finset Push.AbsoluteSums
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {M Ω I : Type}

def ownerBlock (P : Rep G n) (J : Finset M) (S : M → Support n)
    (F : Ω → M → Config G n → ℝ) (u : Ω) (i : ℕ) (U : Config G n) : ℝ :=
  P.activities.K i U * ∏ j ∈ J, flagShare P (S j) i U * F u j U

def enlarged (P : Rep G n) (J : Finset M) (S : M → Support n) (i : ℕ) : Support n :=
  (P.activities.forced i).support ∪ J.biUnion S

def blockInvoice (P : Rep G n) (J : Finset M) (S : M → Support n) (C : M → ℝ)
    (anchor : M) (κ : ℝ) : ℝ :=
  (∏ j ∈ J, P.p.mass (S j) (C j)) * (((S anchor).card:ℝ) * κ)

/-- One majorant for all physical fields and choices of independent sources.
Each eligible host meets every member of its block. The invoice therefore
involves a product of local weights, even for very distant external sites. -/
theorem owner_block_budget (P : Rep G n) (J : Finset M) (anchor : M) (ha : anchor ∈ J)
    (S : M → Support n) (F : Ω → M → Config G n → ℝ) (C : M → ℝ)
    (hC : ∀ j ∈ J, 0 ≤ C j) (hF : ∀ u j, j ∈ J → ∀ U, |F u j U| ≤ C j)
    {κ : ℝ} (hK : P.activities.KBound P.p κ) :
    ∃ bound : ℕ → ℝ, (∀ i, 0 ≤ bound i) ∧
      (∀ u i U, |ownerBlock P J S F u i U| ≤ bound i) ∧
      SumBudget (fun i => P.p.mass (enlarged P J S i) (bound i))
        (blockInvoice P J S C anchor κ) := by
  obtain ⟨b,hb,hroot⟩ := hK
  let Z := fun i => (P.activities.forced i).support
  let eligible := fun i => ∀ j ∈ J, ¬ Disjoint (S j) (P.activities.forced i).inventory
  let D := fun i => if eligible i then b i * ∏ j ∈ J, C j else 0
  let Bill := ∏ j ∈ J, P.p.mass (S j) (C j)
  have billpos : 0 ≤ Bill :=
    prod_nonneg fun j hj => mul_nonneg (Real.exp_nonneg _) (hC j hj)
  have nonneg (i) : 0 ≤ D i := by
    dsimp only [D]; split <;> first | exact le_rfl | exact mul_nonneg (hb i).1 (prod_nonneg hC)
  refine ⟨D,nonneg,?_,?_⟩
  · intro u i U
    by_cases H : eligible i
    · rw [show D i = _ from if_pos H,ownerBlock,abs_mul,abs_prod]
      refine mul_le_mul ?_ (prod_le_prod (fun _ _ => abs_nonneg _) ?_)
        (prod_nonneg (fun _ _ => abs_nonneg _)) (hb i).1
      · simpa only [Real.norm_eq_abs] using (hb i).2 U
      · intro j hj
        rw [abs_mul,abs_of_nonneg (flagShare_nonneg P _ i U)]
        exact (mul_le_of_le_one_left (abs_nonneg _) (flagShare_le_one P _ i U)).trans (hF u j hj U)
    · obtain ⟨j,hj,disj⟩ : ∃ j ∈ J, Disjoint (S j) (P.activities.forced i).inventory := by
        simpa only [eligible,not_forall,exists_prop,not_not] using H
      have vanishes : ∏ t ∈ J, flagShare P (S t) i U * F u t U = 0 :=
        prod_eq_zero hj (by rw [flagShare_support P _ i disj U,zero_mul])
      rw [show D i = 0 from if_neg H,ownerBlock,vanishes,mul_zero,abs_zero]
  · let W := fun i => P.p.mass (Z i) (b i)
    have hW i : 0 ≤ W i := mul_nonneg (Real.exp_nonneg _) (hb i).1
    have pay := Push.Local.sumBudget_meeting (X:=Z) (S anchor) hW hroot
    refine budget_mono (budget_scale billpos pay)
      (fun i => mul_nonneg (Real.exp_nonneg _) (nonneg i)) ?_
    intro i
    by_cases H : eligible i
    · have meets (j) (hj : j ∈ J) : ¬ Disjoint (Z i) (S j) := by
        obtain ⟨x,hx,hxi⟩ := not_disjoint_iff.mp (H j hj)
        exact not_disjoint_iff.mpr ⟨x,(P.activities.forced i).inventory_sup hxi,hx⟩
      rw [show D i = _ from if_pos H,if_neg (fun h => meets anchor ha h.symm)]
      exact (Push.Local.mass_union_meeting (Z i) S J meets C (b i) hC (hb i).1 P.p).trans_eq
        (mul_comm _ _)
    · rw [show D i = 0 from if_neg H,BudgetPoint.mass,mul_zero]
      exact mul_nonneg billpos (pay.1 _)

/-- A product of finite sets of coordinates bounds any finite set of host
assignments. This prices the countably infinite set of independent labels. -/
theorem host_product_budget [Fintype I] (f : I → ℕ → ℝ) (c : I → ℝ)
    (h : ∀ j, SumBudget (f j) (c j)) :
    SumBudget (fun π : I → ℕ => ∏ j, f j (π j)) (∏ j, c j) := by
  apply budget_of_sum (fun π => prod_nonneg (fun i _ => (h i).1 _))
  intro E
  let X := fun i => E.image (fun π => π i)
  have sub : E ⊆ Fintype.piFinset X := fun π hπ =>
    Fintype.mem_piFinset.mpr (fun i => mem_image_of_mem _ hπ)
  apply (sum_le_sum_of_subset_of_nonneg sub
    (fun π _ _ => prod_nonneg (fun i _ => (h i).1 _))).trans
  rw [← Finset.prod_univ_sum X f]
  exact prod_le_prod (fun i _ => sum_nonneg fun _ _ => (h i).1 _)
    (fun i _ => budget_sum (h i) _)

/-- For every proposed grouping into nonempty fibres the distinct real
hosts have a joint absolutely summable, support-weighted price. Each such
host occurs exactly once. All majorants precede all field evaluations. -/
theorem assigned_blocks_budget [Fintype I] (P : Rep G n) (blocks : I → Finset M)
    (anchor : I → M) (occ : ∀ k, anchor k ∈ blocks k) (S : M → Support n)
    (F : Ω → M → Config G n → ℝ) (C : M → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hF : ∀ u j U, |F u j U| ≤ C j) {κ : ℝ} (hK : P.activities.KBound P.p κ) :
    ∃ bound : I → ℕ → ℝ, (∀ k i, 0 ≤ bound k i) ∧
      (∀ u (π : I ↪ ℕ) U, |∏ k, ownerBlock P (blocks k) S F u (π k) U| ≤ ∏ k, bound k (π k)) ∧
      SumBudget (fun π : I ↪ ℕ => ∏ k, P.p.mass (enlarged P (blocks k) S (π k)) (bound k (π k)))
        (∏ k, blockInvoice P (blocks k) S C (anchor k) κ) := by
  choose bound nonneg values bills using fun k => owner_block_budget P (blocks k) (anchor k) (occ k)
    S F C (fun j _ => hC j) (fun u j _ U => hF u j U) hK
  refine ⟨bound,nonneg,?_,?_⟩
  · intro u π U
    rw [abs_prod]
    exact prod_le_prod (fun _ _ => abs_nonneg _) (fun k _ => values k u _ U)
  · exact budget_pull (fun π : I ↪ ℕ => (π : I → ℕ)) DFunLike.coe_injective
      (host_product_budget _ _ bills)

end YM.Integration.FVA1Physical.Marked
