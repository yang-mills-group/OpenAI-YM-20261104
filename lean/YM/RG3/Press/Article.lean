import YM.RG3.Ink.Priced
import YM.Extra.MULTISOURCE_TRAJECTORIES.Bands
import YM.Push.CORRECTED_COLUMNS.Pad

/-!
# RG_03: Publishing a re-expression in the complete budget

Forced-only portion; operates also when publishing onto a *fixed* vacuum
Rep. For global mark-only additive terms see `Layout`. Preserve slots even
when alternatives share one forced address. Exact forced exclusion is still
on the target support (which must match the original). `Article.cluster` is
the same convention *before* publishing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Press
open Wilson RG Lattice Overlay Extra.Trajectories Finset Function Marker MeasureTheory Ac Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} (α : Type*) {V : Type*} [DecidableEq V] {R : Census V}

structure Article (p : BudgetPoint) (G : Gauge) (R : Census V) (v : V → Site n) where
  address : α → ForcedAddress G n
  flow : α → Config G n → Poly R

namespace Article
variable {α} {p : BudgetPoint} {v : V → Site n} (d : Article α p G R v) (P : Rep G n)

abbrev span (i : α) := (d.address i).support
abbrev inv (i : α) := (d.address i).inventory

theorem span_ne (i : α) : (d.span i).Nonempty := (d.address i).inventory_ne.mono (d.address i).inventory_sup

structure Sound : Prop where
  payload i : Width.LocalCharge p v (d.span i) (d.flow i)
  ready i U : d.flow i U ≠ 0 → (d.address i).eligible p.threshold U
  honest i U : ((d.flow i U).part R.quiet).im = 0
  query i : MeasurableSet {U | (d.address i).extraTest U}
  invariantTest i k U : (d.address i).extraTest (Lattice.gauge k U) ↔ (d.address i).extraTest U
  reads i : UsesFinal p.threshold (d.span i) (d.address i).extraTest

variable (w : V → ℝ) (A : ℝ)

def Budget := ∃ y : α → Poly R, (∀ i U, Width.Covered (d.flow i U) (y i)) ∧
    Hit d.span p.B (fun i => Poly.price w (y i)) p.supportExponent A

def room (U : Config G n) (s : Finset α) :=
    (s : Set α).PairwiseDisjoint d.span ∧ s.biUnion d.inv = flags p.threshold U

open scoped Classical in
def pack (U : Config G n) (s : Finset α) := if d.room U s then ∏ i∈s,d.flow i U else 0

def cluster (U : Config G n) := ∑' s,d.pack U s

-- arbitrary route. No coordinate dictionary postulated beyond actual
-- predicates and shape. Does not assert traceable/blank reservoir in H.
structure Hosting (slot : α → ℕ) : Prop where
  clock : P.p=p
  equal_span i : d.span i = (P.activities.forced (slot i)).support
  equal_inv i : d.inv i = (P.activities.forced (slot i)).inventory
  accepts i U : d.flow i U ≠ 0 → (P.activities.forced (slot i)).extraTest U

variable (slot : α → ℕ)

def broth (i : ℕ) (U : Config G n) := ∑' c : {c // slot c=i}, (d.flow c.val U).part R.quiet

def stream (i : ℕ) (U : Config G n) := ∑' c : {c // slot c=i}, d.flow c.val U

theorem flow_abs {w A} (hw : ∀ i, 0<w i) (hd : d.Budget w A) (U) : Summable fun c => Poly.price w (d.flow c U) := by
  obtain ⟨y,he,H⟩ := hd
  have hg := Letters.Frame.from_hit p.B p.supportExponent A _ (span_ne d)
    (fun i => Poly.nonnegative hw (y i)) p.exponent_pos.le H
  exact hg.2.1.of_nonneg_of_le (fun i => Poly.nonnegative hw _) (fun i => (he i U).reprice w hw)

theorem stream_part_quiet {w A} (hw : ∀ i, 0<w i) (hd : d.Budget w A) (i : ℕ) (U) :
    (d.stream slot i U).part R.quiet=d.broth slot i U := by
  unfold stream broth
  exact Poly.share (((Poly.budgeted hw (d.flow_abs hw hd U) (fun _ => le_rfl)).1).comp_injective Subtype.val_injective) _

theorem selection (h : d.Hosting P slot) (U : Config G n) (s : Finset α) :
    Packets.selected slot (P.activities.admissible P.p U) s ↔ d.room U s := by
  have he : (s.image slot).biUnion (fun i => (P.activities.forced i).inventory)=s.biUnion d.inv := by
    ext1 x; simp only [mem_biUnion,mem_image, exists_exists_and_eq_and, ← h.equal_inv]
  unfold Packets.selected room Activities.admissible
  rw [he,h.clock]; constructor
  · rintro ⟨⟨ha,hb⟩,hc⟩
    refine ⟨fun i hi j hj hn => ?_,hb⟩
    dsimp only [onFun]; rw [h.equal_span, h.equal_span]
    exact ha (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) (fun h' => hn (hc hi hj h'))
  rintro ⟨ha,hb⟩
  refine ⟨⟨?_,hb⟩,?_⟩
  · intro i hi j hj hn
    obtain ⟨i,hI,rfl⟩ := mem_image.mp hi; obtain ⟨j,hJ,rfl⟩ := mem_image.mp hj
    rw [← h.equal_span,← h.equal_span]
    exact ha hI hJ (fun e => hn (congrArg _ e))
  intro i hi j hj e
  by_contra hn
  have ht := ha hi hj hn
  dsimp only [onFun] at ht
  rw [h.equal_span, h.equal_span, e, ← h.equal_span] at ht
  obtain ⟨x,hx⟩ := span_ne d j
  exact disjoint_left.mp ht hx hx

open scoped Classical in
theorem repacked {w A} (hw : ∀ i, 0<w i) (h : d.Hosting P slot) (hd : d.Budget w A) (U : Config G n) :
    HasSum (fun s => if P.activities.admissible P.p U s then ∏ i∈s,d.stream slot i U else 0) (d.cluster U) := by
  classical
  let F i := d.flow i U
  have hf := d.flow_abs hw hd U
  have HH := Packets.repack slot (P.activities.admissible P.p U) F (Packets.summable_value slot _ _ hw hf)
    (Poly.budgeted hw hf (fun _ => le_rfl)).1
  have he s : Packets.value slot (P.activities.admissible P.p U) F s=d.pack U s := by
    unfold Packets.value pack
    split_ifs with H H' H'
    · rfl
    · exact (H' ((d.selection P slot h U s).1 H)).elim
    · exact (H ((d.selection P slot h U s).2 H')).elim
    rfl
  unfold cluster; simp_rw [←he]; exact HH

end Article
end YM.RG3.Press
