import YM.RG02.Marker.Connect

/-!
# A derivative with a mode held fixed

Looking at a single coefficient, we can remove a single mark from its
explicit square-free expression even though this isn't a derivation on
the marker quotient. The correct derivative calculus here uses `factor`
multiplication as an adaptor.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG02.Remove
open Marker Extra.Trajectories Marks Finset Primitives.GCC.Anchor
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι] {B : Census ι}

def factor (B : Census ι) (i : ι) := Poly.send (B.fire i) 1

def shave (p : B.Mode) (i : ι) : B.Mode := ⟨p.val.erase i, B.down p.property _ (erase_subset ..)⟩

def lower (x : Poly B) (i : ι) := Poly.inject (R:=B) fun s => by
  classical
  exact if h : i ∉ s.val ∧ insert i s.val ∈ B.choices then x.part ⟨insert i s.val,h.2⟩ else 0

lemma put_back (i : ι) (x : Poly B) (p : B.Mode) (hi : i∈p.val) :
    (lower x i).part (shave p i) = x.part p := by
  classical
  unfold lower Poly.part Poly.inject shave; dsimp only; split
  next h =>
    congr
    exact insert_erase hi
  next h => exact (h ⟨notMem_erase i _,by rw [insert_erase hi]; exact p.property⟩).elim

theorem restores (x : Poly B) (i : ι) (t : B.Mode) :
    (factor B i*x).part t=if i∈t.val then x.part (shave t i) else 0 := by
  rw [factor,mul_at_part]
  have he : diff t (B.fire i).val=shave t i := Subtype.ext (by simp [diff,shave,Census.fire,sdiff_singleton_eq_erase])
  by_cases h : i∈t.val
  · rw [he,if_pos h, if_pos (show (B.fire i).val ⊆ t.val from singleton_subset_iff.mpr h),one_mul]
  rw [if_neg h, if_neg (fun H => h (H (mem_singleton_self ..)))]

theorem regains (x : Poly B) (i : ι) : factor B i * lower x i = euler i x := by
  ext s; rw [part_euler, restores]; split
  next h => exact put_back i x s h
  rfl

lemma up_to {x y : Poly B} (i : ι) (p : B.Mode) (hi : i∈p.val) (h : factor B i*x=factor B i*y) :
    UpTo (shave p i).val x y := by
  intro s hs
  let t : B.Mode := ⟨insert i s.val,B.down p.property _ (insert_subset hi (hs.trans (erase_subset ..)))⟩
  have ht : i∈t.val := mem_insert_self ..
  have he := congrArg (fun v : Poly B => v.part t) h
  rw [restores,restores,if_pos ht,if_pos ht] at he
  have hr : shave t i = s := Subtype.ext (erase_insert (fun H => notMem_erase _ _ (hs H)))
  rwa [hr] at he
end YM.RG02.Remove
