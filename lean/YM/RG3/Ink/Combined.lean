import YM.RG3.Letters.Identity
import YM.Work.H03
import YM.Push.CORRECTED_COLUMNS.Pieces -- Width.Covered and LocalCharge
import YM.Extra.MULTISOURCE_TRAJECTORIES.Algebra -- pass_add etc

/-!
# RG_03: Actual attachment merger, in the marker algebra, with the vacuum

Unlike `YM.Push.Corrected.AddedHeads`, attaching letters may have arbitrary
overlaps (p. 28402+ in comparison manuscript); may have a field-independent
coefficient; may have a vacuum part. Price later. Countably many hard letters.
Slips take all values in a **finite** alphabet on this torus (we will group
countable corrections with the same evaluation support, with absolute price
on *all* contributions and exact retained predicates). There is no finiteness
factor per support in the hit estimate to come.

`Shelf` remains on functions on the gauge group and the exact flags at the
chosen `BudgetPoint`. `Stock` carries the complete K alternatives including the
vacuum and exclusions. When multiplying the exponent by a correction, keep
the *whole* discrepancy factor at this fixed field on its paid support. A
submission with a nonzero quiet mode can change the vacuum representation (but
not thereby the scalar normalization or coupling). Publishes actual entries of
this same unnormalized polynomial onto the new forced labels, with locality,
origins, zero/equality tests all pointwise.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG3.Ink
open Function Set RG Ac Lattice Wilson Marker MeasureTheory Push.Corrected
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {ι : Type*} {μ : Type*} {V : Type*} [DecidableEq V] {R : Census V}
variable (G : Gauge) (n : Side)

/-- Complete input skeleton on the actual fields. Hard supports do not
change within `stockpile`. Supply a separate address change for that. -/
structure Shelf (ι μ : Type*) where
  hard : ι → ForcedAddress G n
  shade : μ → Support n
  nonempty (j : μ) : (shade j).Nonempty

variable {G n} (A : Shelf G n ι μ)
variable (p : BudgetPoint) (R : Census V) (v : V → Site n)

namespace Shelf

def frame : Letters.Frame n (ι ⊕ μ) := {
    read := Sum.elim (fun i => (A.hard i).support) A.shade
    need := Sum.elim (fun i => (A.hard i).inventory) (fun _ => ∅)
    subset := by rintro (i|j); exact (A.hard i).inventory_sup; exact Finset.empty_subset _
    nonempty := by rintro (i|j); exact (A.hard i).inventory_ne.mono (A.hard i).inventory_sup; exact A.nonempty j }

@[simp] theorem inl_hard (i : ι) : A.frame.Hard (Sum.inl i) := (A.hard i).inventory_ne
@[simp] theorem inr_hard (j : μ) : ¬ A.frame.Hard (Sum.inr j) := Finset.not_nonempty_empty

abbrev Patch := A.frame.Patch

/-- Eligibility and actual function constrain stock values and addresses on
the same flags. Preserve all extraTests AGAIN on the merged address. -/
structure Stock where
  hardVal : ι → Config G n → Poly R
  slipVal : μ → Config G n → Poly R
  hardLocal (i) : Width.LocalCharge p v (A.hard i).support (hardVal i)
  hardCharged i U : hardVal i U ≠ 0 → (A.hard i).eligible p.threshold U
  slipLocal (i) : Width.LocalCharge p v (A.shade i) (slipVal i)
  flagged i U : slipVal i U ≠ 0 → ¬ Healthy p.threshold (A.shade i) U

namespace Stock
variable {A p R v} (X : A.Stock p R v)

def ink : (ι ⊕ μ) → Config G n → Poly R := Sum.elim X.hardVal X.slipVal

def cargo (c : A.Patch) (U : Config G n) : Poly R :=
  A.frame.merged (flags p.threshold U) (fun i => X.ink i U) c

def cargoAddr (A : Shelf G n ι μ) (p : BudgetPoint) (c : A.Patch) : ForcedAddress G n := {
  support := A.frame.ground c
  inventory := A.frame.owns c
  inventory_ne := A.frame.owns_nonempty c
  inventory_sup := A.frame.owns_inside c
  extraTest := fun U => ∀ i, Sum.inl i ∈ A.frame.letters c → (A.hard i).eligible p.threshold U }

-- use LocalCharge product theorem including nonzero-origin through whole Poly (not price products at a common U later; supply coefficient majorants separately).
theorem localInk (i : ι ⊕ μ) : Width.LocalCharge p v (A.frame.read i) (X.ink i) := by
  cases i with
  | inl i => exact X.hardLocal i
  | inr i => exact X.slipLocal i

theorem localCargo (c : A.Patch) :
    Width.LocalCharge p v (cargoAddr A p c).support (X.cargo c) := by
  classical
  let W := cargoAddr A p c
  let F := fun U => ∏ j ∈ A.frame.letters c, X.ink j U
  have hF : Width.LocalCharge p v W.support F :=
    Width.product_local (A.frame.letters c) X.ink fun j h =>
      (X.localInk j).widen (A.frame.entries_inside _ h)
  have he U : X.cargo c U = if W.support ∩ flags p.threshold U = W.inventory then F U else 0 := rfl
  refine ⟨fun k U => ?_, ?_, fun U U' h ht => ?_, fun U z hh => ?_⟩
  · rw [he,he,gauge_flags,hF.gauge k U]
  · let W' : ForcedAddress G n := { W with extraTest := fun _ => True }
    have hm : MeasurableSet {U : Config G n | W.support ∩ flags p.threshold U = W.inventory} := by
      simpa only [ForcedAddress.eligible,W',and_true] using Work.H03.eligible_measurable p.threshold W'
        (show MeasurableSet {U : Config G n | True} from MeasurableSet.univ)
    simp_rw [funext he]
    exact Measurable.ite hm hF.borel measurable_const
  · change W.support ∩ flags p.threshold U = W.support ∩ flags p.threshold U' at ht
    simp only [he, ht]; split
    · exact hF.reads U U' h ht
    rfl
  rw [he] at hh
  split at hh
  · exact hF.carry U z hh
  exact (hh (Poly.part_nil z)).elim

theorem cargo_eligible (c : A.Patch) (U : Config G n) (h : X.cargo c U ≠ 0) :
    (cargoAddr A p c).eligible p.threshold U := by
  unfold cargo Letters.Frame.merged at h
  split at h
  · rename_i he
    refine ⟨he, fun i hi => X.hardCharged i U fun hh => h (Finset.prod_eq_zero hi hh)⟩
  contradiction

def pack (U : Config G n) (s : Finset A.Patch) :=
  A.frame.after (flags p.threshold U) (fun i => X.ink i U) s

open scoped Classical in
def tray (U : Config G n) (s : Finset ι) : Poly R := if
    (s : Set ι).PairwiseDisjoint (fun i => (A.hard i).support) ∧
      s.biUnion (fun i => (A.hard i).inventory) = flags p.threshold U
    then ∏ i ∈ s, X.hardVal i U else 0

-- Split the selection universe again to the original hard gas and a
-- distinct-letter factor per correction. Useful with a finite correction
-- alphabet even when the old K & E alphabets are countably infinite.
theorem disjSum_tray (U : Config G n) (s : Finset ι) (z : Finset μ) :
    A.frame.before (flags p.threshold U) (fun i => X.ink i U) (s.disjSum z) =
      X.tray U s * ∏ i ∈ z, X.slipVal i U := by
  classical
  let F := flags p.threshold U
  have hI : A.frame.inventory (s.disjSum z) = s.biUnion (fun i => (A.hard i).inventory) := by
    ext x; rw [Letters.Frame.inventory,Finset.mem_biUnion,Finset.mem_biUnion]; constructor
    · rintro ⟨(i|j),hi,H⟩
      · exact ⟨i,Finset.inl_mem_disjSum.mp hi,H⟩
      exact False.elim (Finset.notMem_empty _ H)
    rintro ⟨i,hi,H⟩; exact ⟨Sum.inl i,Finset.inl_mem_disjSum.mpr hi,H⟩
  have hv : A.frame.OldOK (s.disjSum z) ↔
      (s : Set ι).PairwiseDisjoint (fun i => (A.hard i).support) := by
    constructor
    · intro h i hi j hj hn; exact h (Finset.inl_mem_disjSum.mpr hi)
        (Finset.inl_mem_disjSum.mpr hj) (Sum.inl_injective.ne hn) (A.inl_hard i) (A.inl_hard j)
    intro h
    rintro (i|i) hi (j|j) hj hn h1 h2
    · exact h (Finset.inl_mem_disjSum.mp hi) (Finset.inl_mem_disjSum.mp hj) (fun hE => hn (congr_arg _ hE))
    · exact (A.inr_hard _ h2).elim
    · exact (A.inr_hard _ h1).elim
    exact (A.inr_hard _ h1).elim
  simp only [Letters.Frame.before, tray, Letters.Frame.ValidOld, hv, Letters.Frame.Covers, hI]
  split
  next h => rw [Finset.prod_disjSum]; rfl
  next h => rw [zero_mul]

-- local summability proofs; all dependences on #modes from finite dimensional topology are used *only* to obtain summability from absolute tests
-- and never to produce weighted estimates.
lemma bill_alternatives [Fintype μ] (U : Config G n) (h : Summable fun b => ‖X.tray U b‖) :
    Summable fun j : Finset ι × Finset μ => ‖X.tray U j.1 * ∏ i ∈ j.2, X.slipVal i U‖ := by
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
  simp_rw [tsum_fintype]
  refine summable_sum fun s _ => ?_
  let T := ∏ i ∈ s, X.slipVal i U
  let J := LinearMap.toContinuousLinearMap (Algebra.lmul ℂ _ T)
  exact (h.mul_left ‖J‖).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by rw [mul_comm]; exact J.le_opNorm _)

private def separateSet : Finset ι × Finset μ ≃ Finset (ι ⊕ μ) := {
  toFun := fun j => j.1.disjSum j.2
  invFun := fun j => (j.toLeft,j.toRight)
  left_inv := by intro j; simp
  right_inv := fun _ => Finset.toLeft_disjSum_toRight }

/-- Hold the field throughout. Covers vacuum/marked gas simultaneously.
Exact unnormalized factor identity, with termwise summability in finite-mode
topology; budgets with uniform dependence on the modes will be separate. -/
theorem stockpile [Fintype μ] (U : Config G n) (h : Summable fun b => ‖X.tray U b‖) :
    Summable (fun q : Finset A.Patch => ‖X.pack U q‖) ∧
    (∑' b, X.tray U b)*(∏ i : μ, (1 + X.slipVal i U)) = ∑' q, X.pack U q := by
  classical
  let g (i : ι ⊕ μ) := X.ink i U
  let F := flags p.threshold U
  have hf : ∀ i, ¬ A.frame.Hard i → g i ≠ 0 → ¬ Disjoint (A.frame.read i) F := by
    rintro (i|j) hi
    · exact (hi (A.inl_hard i)).elim
    exact X.flagged j U
  have hi := (A.frame.reindex F g hf (fun i => i) rfl).2
  have he := (A.frame.reindex F g hf norm norm_zero).1
  let B (s : Finset (ι ⊕ μ)) := A.frame.before F g s
  change (∑' s, B s) = ∑' s,X.pack U s at hi
  have hv (j : Finset ι × Finset μ) : B (separateSet j) =
      X.tray U j.1 * ∏ i ∈ j.2, X.slipVal i U := X.disjSum_tray ..
  let q := X.bill_alternatives U h
  refine ⟨he.mp (separateSet.summable_iff.mp (show Summable (fun j : Finset ι × Finset μ => ‖B (separateSet j)‖) from
    q.congr fun i => (congr_arg _ (hv i)).symm)), Eq.trans ?_ hi⟩
  letI : IsTopologicalSemiring (Poly R) := {}
  calc
    _ = ∑' b, (X.tray U b * ∏ i : μ, (1 + X.slipVal i U)) := (Summable.tsum_mul_right _ h.of_norm).symm
    _ = ∑' b, ∑' z : Finset μ, (X.tray U b * ∏ i ∈ z, X.slipVal i U) := tsum_congr fun b => by
      rw [Finset.prod_one_add, Finset.mul_sum, Finset.powerset_univ, tsum_fintype]
    _ = ∑' j : Finset ι × Finset μ, (X.tray U j.1 * ∏ i ∈ j.2, X.slipVal i U) := q.of_norm.tsum_prod.symm
    _ = ∑' j : Finset ι × Finset μ, B (separateSet j) := tsum_congr fun i => (hv i).symm
    _ = _ := separateSet.tsum_eq _

end Stock
end Shelf
end YM.RG3.Ink
