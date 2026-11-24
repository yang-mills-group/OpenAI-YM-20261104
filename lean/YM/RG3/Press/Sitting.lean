import YM.RG3.Press.Directory
import YM.Progress.DIRECTED_RECIPE.Pellets
/-!
# Pure marked moves on a fixed vacuum

Can even fit on the sleepK labels of a UV folio when they're *not known
to be asleep*. Regular overlays may be rewritten independently (v and
vac E not). `Article.publish` will combine routed values even if one of
the arbitrary parking places is also an old address carrying vacuum K
or another marked K.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Press
open Lattice Wilson RG Overlay Extra.Trajectories Marker Finset Function MeasureTheory Ac Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
open RG3.Ink
variable {n : Side} {G : Gauge} {μ : Type*}
variable {V : Type*} [DecidableEq V] {R : Census V} {p : BudgetPoint} {v : V → Site n}
variable (P : Rep G n)

/-- Weaker than Gather's `Aperture`. Existing address dictionary has
some label by shape whose extraTest always passes *whenever eligible by
primary flag test*. This is enough to publish onto that label using Bands
`each`. Does not assert there from C.Makes. -/
def Accessible := ∀ a : ForcedAddress G n, ∃ i, a.support = (P.activities.forced i).support ∧
  a.inventory = (P.activities.forced i).inventory ∧ (∀ U, a.support∩flags P.p.threshold U=a.inventory → (P.activities.forced i).extraTest U)

lemma access_aperture (h : Aperture P) : Accessible P := by
  intro i
  obtain ⟨j,hj,h⟩ := h ⟨i.support,i.inventory,i.inventory_ne,i.inventory_sup⟩
  exact ⟨j,hj.symm,h.1.symm,fun U _ => h.2 U⟩

open Progress.DirectedRecipe Ovens in
lemma access_folio {p : BudgetPoint} (hp : P.p=p)
    (h : P.activities.forced= Pipes.addr (folio G n) p) : Accessible P := by
  intro i
  have h' := tile_exact (G:=G) p (readFoot i) 0
  rw [h,hp]
  exact ⟨sleepK G n (readFoot i,0), (congrArg Foot.support h').symm,
    (congrArg Foot.inventory h').symm, fun U h => (tile_test p _ _ U).mpr h⟩

variable [DecidableEq μ] {W : Shelf G n ℕ μ} (X : W.Stock p R v)

def lone (W : Shelf G n ℕ μ) (i : ℕ) : W.Patch :=
  ⟨{Sum.inl i},by
    refine ⟨⟨singleton_nonempty _,?_⟩, ⟨_,mem_singleton_self _,W.inl_hard i⟩,fun a ha b hb hg => ?_⟩
    · simp only [mem_singleton]; rintro a rfl b rfl; exact .refl
    exact (hg ((mem_singleton.mp ha).trans (mem_singleton.mp hb).symm)).elim⟩

omit [DecidableEq μ] in
lemma lone_inj : Injective (lone W) := fun _ _ h => Sum.inl.inj (singleton_inj.mp (congrArg W.frame.letters h))

/-- A component without a slip letter does not relabel a whole overlapping
set---it HAS to be a singleton old K. This is independent of markers. -/
lemma extra_mark (a : W.Patch) (h : ¬∃ i, a = lone W i) : ∃ i : μ,Sum.inr i ∈ W.frame.letters a := by
  by_contra! hc
  have he j (hj : j∈W.frame.letters a) : W.frame.Hard j := by
    cases j with
    | inr i => exact (hc i hj).elim
    | inl i => exact W.inl_hard i
  obtain ⟨i,hi'⟩ := a.property.1.1
  have hi : i∈W.frame.letters a := hi'
  rcases i with i|i
  swap; exact hc i hi
  refine h ⟨i,Subtype.ext (eq_singleton_iff_unique_mem.mpr ⟨hi',fun j hj => ?_⟩)⟩
  have hh := a.property.1.2 _ hi _ hj
  clear hj
  induction hh with
  | refl => rfl
  | tail _ h' IH =>
    obtain ⟨hk,hl,x,hx,hx'⟩ := h'
    rw [IH] at hk hx
    by_contra hn
    exact disjoint_left.mp (a.property.2.2 hi hl (Ne.symm hn) (he _ hi) (he _ hl)) hx hx'

lemma silent (hs : ∀ i U, (X.slipVal i U).part R.quiet=0) (a : W.Patch) (h : ¬ ∃ i,a=lone W i) (U : Config G n) :
    (X.cargo a U).part R.quiet=0 := by
  classical
  unfold Shelf.Stock.cargo Letters.Frame.merged; split
  · obtain ⟨i,hi⟩ := extra_mark a h
    let Q : Poly R →* ℂ := { toFun := fun x => x.part R.quiet, map_one' := by simp, map_mul' := fun _ _ => Poly.quiet_mul .. }
    exact (map_prod Q ..).trans (prod_eq_zero hi (show Q (X.slipVal i U)=0 from hs i U))
  rfl

omit [DecidableEq μ] in
lemma lone_toner (i : ℕ) (U : Config G n) : X.cargo (lone W i) U=X.hardVal i U := by
  classical
  have ha : W.frame.letters (lone W i)={Sum.inl i} := rfl
  unfold Shelf.Stock.cargo Letters.Frame.merged
  simp_rw [Letters.Frame.ground,Letters.Frame.owns,Letters.Frame.footprint,Letters.Frame.inventory,ha,
    singleton_biUnion,prod_singleton]
  split
  · rfl
  next h => exact (not_ne_iff.mp fun hh => h ((X.hardCharged i U hh).1)).symm

open scoped Classical in
def wharf (h : Accessible P) (c : W.Patch) : ℕ := if he : ∃ i,c=lone W i then he.choose else
    (h (Shelf.Stock.cargoAddr W p c)).choose

omit [DecidableEq μ] in
@[simp] lemma wharf_lone (h : Accessible P) (i : ℕ) : wharf (p:=p) P h (lone W i) = i := by
  unfold wharf; rw [dif_pos (show ∃ j,lone W i = lone W j from ⟨i,rfl⟩)]
  apply (lone_inj (W:=W))
  exact (show lone W i = _ from Exists.choose_spec (p:=fun j => lone W i=lone W j) ⟨i,rfl⟩).symm
omit [DecidableEq μ] in
lemma wharf_other (h : Accessible P) (a : W.Patch) (ha : ¬∃ i,a=lone W i) :
    wharf (p:=p) P h a = (h (Shelf.Stock.cargoAddr W p a)).choose := dif_neg ha

omit [DecidableEq μ] in
lemma wharf_fit (h : Accessible P) (hp : P.p=p) (hK : W.hard=P.activities.forced) :
    (stamp X).Hosting P (wharf (p:=p) P h) := by
  classical
  let B := stamp X
  have he i : B.span (lone W i)=(W.hard i).support := show ({Sum.inl i} : Finset (ℕ⊕μ)).biUnion _ = _ from by rw [singleton_biUnion]; rfl
  have ha i : B.inv (lone W i)=(W.hard i).inventory := show ({Sum.inl i} : Finset (ℕ⊕μ)).biUnion _ = _ from by rw [singleton_biUnion]; rfl
  have ht (i : W.Patch) (_h' : ¬∃ j,i=lone W j) := (h (B.address i)).choose_spec
  change B.Hosting _ _; refine ⟨hp,?_,?_,?_⟩ <;> intro i
  all_goals
    by_cases hi : ∃ j,i=lone W j
  · obtain ⟨i,rfl⟩ := hi; rw [wharf_lone,he,hK]
  · exact (wharf_other (p:=p) P h i hi).symm ▸ (ht i hi).1
  · obtain ⟨i,rfl⟩ := hi; rw [wharf_lone,ha,hK]
  · exact (wharf_other (p:=p) P h i hi).symm ▸ (ht i hi).2.1
  · obtain ⟨i,rfl⟩ := hi; rw [wharf_lone,←hK]
    intro U hf
    exact (X.hardCharged i U (by rw [← lone_toner X i U]; exact hf)).2
  intro U hf; rw [wharf_other P h _ hi]
  apply (ht i hi).2.2 U
  rw [hp]; exact (X.cargo_eligible i U hf).1

lemma wharf_eq (h : Accessible P) (hs : ∀ i U,(X.slipVal i U).part R.quiet=0)
    (hh : ∀ i U,(X.hardVal i U).part R.quiet=(P.activities.K i U:ℂ)) (i U) :
    (stamp X).broth (wharf (p:=p) P h) i U = (P.activities.K i U:ℂ) := by
  let c : {c // wharf (p:=p) P h c=i} := ⟨lone W i,wharf_lone P h _⟩
  unfold Article.broth; rw [tsum_eq_single c]
  · change (X.cargo (lone W i) U).part _=_; rw [lone_toner,hh i U]
  intro k hk
  apply silent X hs _ _ U
  rintro ⟨j,hj⟩
  apply hk; apply Subtype.ext
  have hj' := k.property
  rw [hj,wharf_lone] at hj'; exact hj.trans (congrArg (lone W) hj')

end YM.RG3.Press
