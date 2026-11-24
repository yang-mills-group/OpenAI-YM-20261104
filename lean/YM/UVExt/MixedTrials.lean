import YM.UVExt.FiniteFirst
import YM.UVExt.GridDifference
import YM.Push.RELAY_DIFFERENCE.RawTop
import YM.MergeProof.Portions

/-!
# Differencing a single trial and its top budget

This operates on literal cylinders on their actual lattice. Each additional forward difference
here costs one additional weight e+1. Subsequent modules differentiate multiple insertions and
assemble products with slot-by-slot comparison quantifiers, not pooling a weight truncation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExt.Slots
open Set Function Filter Lattice Wilson RG Overlay Next.Foundations Bid Extraction Extraction.Lease
open Push.RelayDifference
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {d e : ℕ} {o : Extraction.Order}

def next (a : Axis) (F : Trial C) : Trial C :=
  fun N p x=> (C.S.a N:ℂ)⁻¹ • (F N p (x+Lattice.step a)-F N p x)
def mixed : List Axis → Trial C → Trial C
| [], F=> F
| a::A, F=> next a (mixed A F)
def slotField (x : C.book.Token) (w : List Axis) : Trial C := mixed w (visits C x.1 x.2)
variable {F : Trial C}
lemma stencilled_next (H : Stencilled o F) (a : Axis) : Stencilled o (next a F) := by
  obtain ⟨X,h⟩ := H
  exact ⟨X.image (fun x=>x+Lattice.step a) ∪ X, h.mono (fun i hi => ((hi.step a).sub hi).smul _)⟩
lemma stencilled_mixed (H : Stencilled o F) (w : List Axis) : Stencilled o (mixed w F) := by
  induction w with
  | nil=>exact H
  | cons p l h=>exact stencilled_next h p
lemma mixed_cont (H : ∀ N p x, Continuous (F N p x)) (w : List Axis) : ∀ N p x, Continuous (mixed w F N p x) := by
  induction w with
  | nil=>exact H
  | cons p l h=>exact fun i j x => ((h i j (x+step p)).sub (h i j x)).const_smul _
lemma slot_continuous (b : C.book.Token) (w : List Axis) : ∀ N p x, Continuous (slotField b w (C:=C) N p x) :=
    mixed_cont (fun _ _ _=> C.continuousO ..) w

lemma unpriced_next {N p : ℕ} (x : Site (C.side N p)) (a : Axis) :
    unpriced C (next a F) (d+1) N p x = unpriced C F d N p (x+step a)-unpriced C F d N p x := by
  dsimp only [next,unpriced,Push.RelayDifference.weight]
  have ht : (C.S.a N:ℂ) ≠ 0 := by exact_mod_cast (C.S.a_pos N).ne'
  rw [pow_succ,smul_smul, mul_assoc,mul_inv_cancel₀ ht,mul_one,smul_sub]
lemma protected_next (H : shiftCosts C o) (a : Axis) {F : Trial C} (hf : RawProtected C o F d) :
    RawProtected C o (next a F) (d+1) := by
  obtain ⟨X,hX,c,b,hc,hb,H'⟩ := hf
  let D := X.image (fun x => x + step a) ∪ X
  let t (i : Cutoffs) := jump (C.path.levels.budget i.1)
  have ht : Slow C o t := H
  refine ⟨D,Finset.mem_union_right _ hX,_,_,(ht.mul hc).add hc,hb.add hb,?_⟩
  exact H'.mono fun j hh => hh.mono fun i hi x => by
    obtain ⟨hx,hA,hB,hU⟩ := hi x
    obtain ⟨hy,hY,hQ,hv⟩ := hi (x+step a)
    have hD : regional X (x+step a) ⊆ regional D x := by
      rintro q hq
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_image.mpr ⟨_,Finset.mem_union_left _ (Finset.mem_image_of_mem _ hy), by rw [map_add,wrap_step]; abel⟩
    have hD' : regional X x ⊆ regional D x := Finset.image_subset_image Finset.subset_union_right
    have hm := regular_larger hy hD
    have hs := regular_larger hx hD'
    have ha : separation (x+step a) x ≤ 1 := by rw [separation, add_comm, add_sub_cancel_right]; exact pdist_step _
    rw [unpriced_next]
    exact ⟨regular_sub hm hs, bound_sub hm hs (bound_larger (dir_shift _ _ _ _ _ ha hY) hD) (bound_larger hA hD'),
      add_nonneg hQ hB, fun U => (norm_sub_le ..).trans (add_le_add (hv U) (hU U))⟩
lemma protectedMixed (H : C.Makes) (hS : G.Simple) (hg : shiftCosts C o) (w : List Axis) (b : C.book.Token) :
    RawProtected C o (slotField b w) (b.1+w.length) := by
  induction w with
  | nil=> exact RawProtected.visits H hS b.2 le_rfl
  | cons p l h=> exact (show _ = (b.1+(p::l).length) from Nat.add_assoc ..) ▸ protected_next hg p h


/-- Slot evaluation is literal finite differencing (torus shifts via the cover). -/
lemma values_are_differenced {n N p : ℕ} (b : C.book.Token) (w : List Axis) (i : Fin n) (y : Grid.Args n) (U) :
    slotField (C:=C) b w N p (wrap (C.side N p) (y i)) U = Grid.mixed (C.S.a N) (w.map fun a=>(i,a))
      (fun r=> C.seen b ((wrap (C.side N p) ∘ r) i) U) y := by
  induction w generalizing y with
  | nil=>rfl
  | cons p v h=>
    unfold slotField mixed
    dsimp only [next, Grid.mixed,Grid.differences,Pi.smul_apply,Pi.sub_apply,List.map_cons]
    change ((C.S.a N : ℂ)⁻¹ * ((slotField (C:=C) b v N _ _ U)-(slotField b v _ _ _ U))) = (↑(C.S.a N)⁻¹:ℂ) * _
    rw [Complex.ofReal_inv, ← h,← h]
    congr 3; rw [Pi.add_apply,map_add]; simp [Grid.jump]
end YM.UVExt.Slots
