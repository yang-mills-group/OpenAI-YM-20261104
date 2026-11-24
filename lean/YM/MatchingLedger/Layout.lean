import YM.Work.E01
import YM.Work.F01
import YM.Push.GRID_APPROXIMATION.Cone

/-!
# Windows for doing local probability estimates

Price one sum at a time on coarse-sites of the *actual* kernel. Fixed-L estimates;
no pre-block-length costs claimed, use with waits. Keep the complete patch stencils even on
small fields. A window needn't be connected.
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger
open Function Filter Lattice RG Wilson Tree Pressure
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius

section volume
variable {ι α : Type*} [Fintype ι] {v : Lattice.Side}

/-- Entries with starting (parent) site in `s`. -/
def located (a : ι → Site v) (s : Support v) : Finset ι := Finset.univ.filter (fun i=>a i∈s)

lemma loc {a : ι → Site v} {s : Support v} {i : ι} : i ∈ located a s ↔ a i ∈ s := by simp [located]
lemma loc_all (a : ι → Site v) : located a Finset.univ=Finset.univ := by simp [located]
lemma total_at (a : ι → Site v) (f : ι → ℝ) (s : Support v) :
    (∑ x∈s, ∑ i ∈ located a {x}, f i) = ∑ i∈ located a s, f i := by
  classical
  simp_rw [located, Finset.sum_filter]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=> ?_
  simp

lemma point_pay (s : Support v) (r : ℕ) (f : Site v → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ∑ x∈s, ∑ i∈halo r {x}, f i ≤ (↑(r+r+1):ℝ)^4 * ∑ i ∈ halo r s, f i := by
  classical
  have he (x) (hx : x ∈ s) (y) (hy : y∈halo r {x}) : y ∈ halo r s :=
    Lattice.Corona.halo_mono le_rfl (Finset.singleton_subset_iff.mpr hx) hy
  calc
    _ = ∑ x∈s, ∑ i∈halo r s, if separation i x ≤ r then f i else 0 := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.sum_filter]; congr 1
      ext i; rw [halo_spec, Finset.mem_filter]; simp only [Finset.mem_singleton, exists_eq_left]; rw [separation_comm x]
      exact ⟨fun hi => ⟨halo_spec.mpr ⟨x,hx,(separation_comm ..).trans_le hi⟩,hi⟩,And.right⟩
    _ ≤ _ := by
      rw [Finset.sum_comm, Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
      rw [← Finset.sum_filter,Finset.sum_const, nsmul_eq_mul]; refine mul_le_mul_of_nonneg_right ?_ (hf _)
      have hi := Finset.card_le_card (show (s.filter fun x=> separation i x ≤ r) ⊆ halo r {i} from
        fun k hk=>halo_spec.mpr ⟨i,Finset.mem_singleton_self _, (Finset.mem_filter.mp hk).2⟩)
      have hp := hi.trans (Lattice.Corona.halo_size {i} r); rw [Finset.card_singleton, Nat.one_mul] at hp
      exact_mod_cast hp

lemma accumulate {i j : Site v} (s : Support v) (r k : ℕ) (hi : i∈halo r s) (he : separation i j ≤ k) :
    j ∈ halo (r+k) s := by
  obtain ⟨x,hx,h⟩:= halo_spec.mp hi
  exact halo_spec.mpr ⟨x,hx,(separation_triangle _ i _).trans (Nat.add_le_add h he)⟩
lemma advance (s : Support v) (r k : ℕ) : halo k (halo r s) ⊆ halo (r+k) s := by
  intro i hi; obtain ⟨x,hx,H⟩ := halo_spec.mp hi; exact accumulate s r k hx H
lemma near_root {i j : Site v} {k : ℕ} : i∈halo k {j} ↔ separation j i ≤ k := by simp only [halo_spec, Finset.mem_singleton, exists_eq_left]
lemma away {R : Support v} {i j : Site v} {r k : ℕ} (h : i ∉ halo (r+k) R) (he : separation i j ≤ k) : j∉halo r R := fun hx => h (accumulate R r k hx ((separation_comm ..).trans_le he))
end volume

variable {c f : Side} (S : StepData c f)

def region {α : Type*} (S : StepData c f) (e : Site f × α) := S.ratio.parent e.1
def area {g : Ratio c f} (F : Forest g) (e : F.Free) := g.parent e.val.1

lemma region_size (R : Support c) (α : Type*) [Fintype α] :
    (located (region (α:=α) S) R).card = Fintype.card α * Fintype.card (Site S.patch.L) * R.card := by
  have h(x:Site f) : (∑ _i:α, if S.ratio.parent x ∈ R then (1:ℝ) else 0)=
      Fintype.card α * (if S.ratio.parent x ∈ R then (1:ℝ) else 0) := by simp
  have he : (∑ i∈located (region (α:=α) S) R, (1:ℝ))= _ :=
    (show _=(Fintype.card α:ℝ) * Fintype.card (Site S.patch.L) * R.card from by
      unfold located; rw [Finset.sum_filter, Fintype.sum_prod_type]; unfold region
      change (∑ x:Site f, ∑ _ : α, if S.ratio.parent x∈R then (1:ℝ) else 0)= _
      simp_rw [h]; rw [← Finset.mul_sum,Work.F01.sum_parent S.ratio (fun u=> if u∈R then (1:ℝ) else 0)]
      rw [← Finset.sum_filter]; have he : (Finset.univ.filter fun i=> i ∈ R)=R := Finset.ext fun i=>by simp
      rw [he, Finset.sum_const, nsmul_eq_mul, mul_one, mul_assoc]; rfl)
  rw [Finset.sum_const,nsmul_eq_mul,mul_one] at he; exact_mod_cast he

lemma free_size (R : Support c) (F : Forest S.ratio) :
    (located (area F) R).card ≤ Fintype.card Axis * Fintype.card (Site S.patch.L) * R.card :=
  (Finset.card_le_card_of_injOn Subtype.val (t:=located (region (α:=Axis) S) R) (fun _ hx=>(loc (a:=region (α:=Axis) S)).mpr ((loc (a:=area F)).mp hx))
    Subtype.val_injective.injOn).trans_eq (region_size S R Axis)

lemma poshop (x : Site f)(i : Axis) : separation (S.ratio.parent x) (S.ratio.parent (x+step i)) ≤ 1 := by
  rw [Ratio.parents_hop S.ratio S.patch.odd_side]; split_ifs; exact Work.E01.sep_step_le ..; simp
lemma near_visit (z : Cell f) (x : Site f) (hx : x ∈ visits z.1 (square z.2.val.1 z.2.val.2)) :
    separation (region S z) (S.ratio.parent x) ≤ 2 := by
  rw [square_corners] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  unfold region
  rcases hx with rfl|rfl|rfl|rfl|rfl
  · simp
  · exact (poshop S _ _).trans (by norm_num)
  · exact le_trans (separation_triangle _ (S.ratio.parent (z.1+step z.2.val.1)) _) (Nat.add_le_add (poshop S _ _) (poshop S _ _))
  · exact (poshop S _ _).trans (by norm_num)
  simp

-- satisfiable on all admitted sizes, no transplanted tree. Adapt `FlatData.crosses_at`:
-- in the erasure comparison use one crossing bond *in each prescribed direction*.
lemma reaching (x : Site c) (a : Axis) : ∃ i : Site f,
    S.ratio.parent i=x ∧ S.ratio.parent (i+step a)=x+step a := by
  let g:=S.ratio; let t := g.count.val/2; let y : Cover := t • step a
  have he : y ∈ box t := by rw [box_iff_layers]; intro i; by_cases h:i=a <;> simp [layers,y,h]
  let b := g.assemble (x,wrap g.count y)
  have hv : g.parent b=x:= g.assemble_parent _
  refine ⟨b,hv,?_⟩
  rw [show S.ratio=g from rfl,g.parents_hop S.patch.odd_side,hv,if_pos]
  rw [show g.residue b=wrap g.count y from g.assemble_res _,g.half_lift S.patch.odd_side y he]; simp [t,y]

lemma hop_ne (x : Site c) (a : Axis) (h : 1 < c.val) : x+step a ≠ x := by
  haveI : Fact (1<c.val) := ⟨h⟩
  intro he
  have h' : step a=(0:Site c) := add_eq_left.mp he
  have h : (1:ZMod c.val)=0:= by simpa using congr_fun h' a
  exact one_ne_zero h

namespace PatchArea
-- In addition to kernel dependencies we keep a peripheral extent sufficient for the chord
-- cost/gap. None of these numbers truncate the theory.
def radius (P : Patch) := Push.GridApprox.reach P + P.L.val + P.J + 8
lemma radius_reach (P : Patch) : Push.GridApprox.reach P + P.L.val ≤ radius P := by unfold radius; omega
lemma radius_jets (P : Patch) : P.J + 8 ≤ radius P := by unfold radius; omega

lemma window_pay (x : Site c) (z : Site f) (hz : z ∈ Push.GridApprox.window (S.ratio.embed x) (Push.GridApprox.reach S.patch)) :
    separation x (S.ratio.parent z) ≤ radius S.patch := by
  have hp := Lattice.Corona.foreshorten S.ratio (S.ratio.embed x) z; rw [Ratio.embed_parent] at hp
  refine le_trans ?_ (radius_reach ..)
  let L:=S.patch.L.val; change L*_ ≤ _+L at hp
  have he := le_mul_of_one_le_left (Nat.zero_le (separation x (S.ratio.parent z))) (show 1 ≤ L from Nat.one_le_of_lt S.patch.L.prop)
  apply he.trans (hp.trans (Nat.add_le_add_right ?_ L))
  obtain ⟨v,hv,rfl⟩:=hz
  rw [separation_comm,separation]; dsimp only; rw [add_sub_cancel_right]; exact Work.E01.pdist_wrap_le hv

variable {G : Gauge} {R : Support c} {U W : Config G f}

def ExteriorEq (R : Support c) (U W : Config G f) : Prop := ∀ i : Bond f, region S i∉ R → U i=W i

include S
lemma through (h : ExteriorEq S R U W) {x : Site c} (hz : x ∉ halo (radius S.patch) R) :
    Agrees (Push.GridApprox.window (S.ratio.embed x) (Push.GridApprox.reach S.patch)) U W := by
  intro e he _; apply h; exact fun hi=>hz (halo_spec.mpr ⟨region S e,hi,(separation_comm ..).trans_le (window_pay S x e.1 he)⟩)
lemma faces (h : ExteriorEq S R U W) (e : Cell f) (he : region S e∉halo (radius S.patch) R) :
    toll U e=toll W e := by
  unfold toll; apply congr_arg G.chord; apply travel_local; intro i hi _; apply h; intro hh; apply he
  refine halo_spec.mpr ⟨region S i,hh,(separation_comm ..).trans_le ((near_visit S e _ hi).trans ?_)⟩
  have h:=radius_jets S.patch; omega
lemma from_free (F : Forest S.ratio) {x y : F.Slice G} (h : ∀ i, i ∉ located (area F) R → x i=y i) :
    ExteriorEq S R (F.drape x) (F.drape y) := by
  intro e he
  by_cases hx : e∈ F.trunks
  · exact (F.on_tree x ⟨_,hx⟩).trans (F.on_tree y ⟨_,hx⟩).symm
  exact ((F.off_tree x ⟨_,hx⟩).trans (h ⟨_,hx⟩ (fun hi=>he ((loc (a:=area F)).mp hi)))).trans (F.off_tree y ⟨_,hx⟩).symm
end PatchArea

end YM.MatchingLedger
