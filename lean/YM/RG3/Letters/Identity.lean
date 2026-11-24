import YM.RG3.Letters.Skeleton

/-!
# Exact full flags for the re-expression (selection equality)

Hold the field fixed through this operation. In particular the same `F`
on both sides will be the actual `flags p.threshold U`; include even every
failed mask and every letter depending on them. This doesn't prove the
merger product costs, or justify any analytic step through a mask; it's the
pointwise identity at fixed field (and the exact reindex for justifying the
sums, though one needs absolute criteria such as in `Ac.Tree` or stronger
downstream). Later specialize also to `Marker.Poly`, on which **zero
divisors are present**.
-/

set_option autoImplicit false
noncomputable section

namespace YM.RG3.Letters.Frame
open Lattice RG Function Finset

variable {n : Side} {ι : Type*} (D : Frame n ι) (F : Support n)
variable {M : Type*} [CommMonoidWithZero M] (f : ι → M)

open scoped Classical in
/-- Complete input selections of hard alternatives and distinct exponential
correction letters, exact old exclusions and flag coverage. -/
def before (s : Finset ι) : M := if D.ValidOld F s then ∏ i ∈ s, f i else 0

open scoped Classical in
/-- Keep the exact intersection test in the published activity (although
redundant at the evaluated gas because its selections have disjoint exact
coverage). -/
def merged (i : D.Patch) : M :=
  if D.ground i ∩ F = D.owns i then ∏ j ∈ D.letters i, f j else 0

open scoped Classical in
def after (s : Finset D.Patch) : M :=
  if D.ValidNew F s then ∏ i ∈ s, D.merged F f i else 0

section Reindex
variable [DecidableEq ι]
variable (h : ∀ i, ¬ D.Hard i → f i ≠ 0 → ¬ Disjoint (D.read i) F)

include h in
theorem before_outside (s : Finset ι) (H : ¬ (D.ValidOld F s ∧ D.Charged s)) :
    D.before F f s = 0 := by
  unfold before
  split
  · rename_i he
    by_contra He
    exact H ⟨he, D.illuminated he.2 fun i hi hI =>
      h i hI fun hh => He (Finset.prod_eq_zero hi hh)⟩
  rfl

omit [DecidableEq ι] in
theorem after_outside (s : Finset D.Patch) (H : ¬ D.ValidNew F s) : D.after F f s = 0 := if_neg H

theorem on_read {s : Finset D.Patch} (H : D.ValidNew F s) :
    D.after F f s = D.before F f (D.flatten s) := by
  rw [after,if_pos H,before,if_pos (D.flat_valid H).1,flatten, prod_biUnion (D.letters_apart H.1)]
  exact prod_congr rfl fun i hi => if_pos (D.stamp H hi)

include h in
/-- The same reindex for proving summability, and with an arbitrary
zero-preserving function applied to each *term*. (Not applying it through
tsum.) Exposes the absolute-price consumer without a norm hypothesis on the
monoid. -/
theorem reindex {L : Type*} [AddCommMonoid L] [TopologicalSpace L] (T : M → L) (hT : T 0 = 0) :
    (Summable (T ∘ D.before F f) ↔ Summable (T ∘ D.after F f)) ∧
    (∑' s : Finset ι, T (D.before F f s)) = ∑' s : Finset D.Patch, T (D.after F f s) := by
  let A : Set (Finset ι) := {s | D.ValidOld F s ∧ D.Charged s}
  let B : Set (Finset D.Patch) := {s | D.ValidNew F s}
  let e : B ≃ A := Equiv.ofBijective (D.readPack F) (D.readPack_bijective F)
  let x := T ∘ D.before F f
  let y := T ∘ D.after F f
  have hx : ∀ i ∉ A, x i = 0 := fun i hi => (congr_arg T (D.before_outside F f h i hi)).trans hT
  have hy : ∀ i ∉ B, y i = 0 := fun i hi => (congr_arg T (D.after_outside F f i hi)).trans hT
  have he : (x ∘ ((↑): A → Finset ι)) ∘ e = y ∘ ((↑) : B → Finset D.Patch) :=
    funext fun s => (congr_arg T (D.on_read F f s.property).symm)
  constructor
  · have hx' := Subtype.val_injective.summable_iff (f:=x) (g:=((↑): A → Finset ι)) (by simpa only [Subtype.range_coe] using hx)
    have hy' := Subtype.val_injective.summable_iff (f:=y) (g:=((↑): B → Finset D.Patch)) (by simpa only [Subtype.range_coe] using hy)
    change Summable x ↔ Summable y
    rw [← hx', ← hy', ← e.summable_iff, he]
  change ∑' s, x s = ∑' s, y s
  calc
    _ = ∑' i:A,x i.val := (tsum_subtype_eq_of_support_subset (fun i hi => by
        by_contra hh; exact hi (hx i hh))).symm
    _ = ∑' i:B,x (e i).val := (e.tsum_eq ..).symm
    _ = ∑' i:B,y i.val := tsum_congr (congr_fun he)
    _ = _ := tsum_subtype_eq_of_support_subset (fun i hi => by by_contra hh; exact hi (hy i hh))

end Reindex
end YM.RG3.Letters.Frame
