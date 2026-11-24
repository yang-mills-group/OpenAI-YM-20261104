import YM.RG3.Script.Tier
import YM.RG3.Render.Bulletin
import YM.RG3.Pan.Beryl
import YM.Push.LOCAL_SPLITTING.Atoms

/-! # Register a short group with address and per-root reserves

All decompositions here are before touching the actual older K. Include
mixed captions and raw constants as entries with masks=false. Supports
and labels preserved even then; one can choose not to enter them here when
leaving as stable instead of comparing to/cancelling with masked entries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press
open Next.Rank.Spindle Ac Extra.Multi Push.AbsoluteSums MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n:Side} {α V:Type*} [DecidableEq V] {R:Census V} (ζ:V→Site n) {G : Gauge}
local notation "hull" => Next.Rank.Spindle.patch

/-- ζ applied during Legal; may represent several positions per mark,
by taking outcomes stratified at fixed occurrence positions, preserving copy
species, never combine at unequal root tuples halfway through. -/
structure Estate (n : Side) (R:Census V) where
  post : ℕ→ Site n
  radius : ℕ → ℕ
  style : ℕ→R.Mode
  hot i : (style i).val.Nonempty

variable (A : Estate n R)
namespace Estate
def region (i:ℕ): Support n:= hull (A.radius i) (A.post i)
lemma full (i) : (A.region i).Nonempty:=⟨A.post i,(doors _).mpr (by simp)⟩
def plan : Stage n R ℕ:=⟨fun i=>⟨A.region i,A.full i,A.style i⟩⟩
def Legal := ∀ i v,v∈(A.style i).val → ζ v∈ A.region i

/-- Catalogue of signed germs comparing placed H/models before the mask
change. In particular to compare the analytic formal answer, enter its terms
(with negative signs) on their TRUE supports and masks or non-masks in the
intended exponent; different output indicators need not be proved equal.
One can also treat finite pieces of the section formula including any shifts
on roots by entering in the same reconstruction; has to FIT on the indicated
common regions and same declared marks. `notice` include all path, address &
test evaluation supports even on captions. -/
structure Truss (ι : Type*) (G : Gauge) where
  filing : ι→ℕ
  notice : ι→Support n
  veiled : ι→ Bool
  song : ι→ Config G n→ℂ
  shifted i : notice i ⊆ A.region (filing i)

namespace Truss
variable {ι : Type*} {A}
variable (T : A.Truss ι G)

def reads (p:BudgetPoint)(i : ι) : Config G n→ℂ := if T.veiled i then masked p.threshold (T.notice i) (T.song i) else T.song i
def strand (p:BudgetPoint) : A.plan.Trace ι G:=⟨T.filing,T.reads p,fun _=> A.full _⟩
structure Laws : Prop where
  loc i : LocalOn ↑(T.notice i) (T.song i)
  Borel i : Measurable (T.song i)
  invariant i: GaugeInvariant (T.song i)
  pins i U v : T.song i U≠0 → v∈(A.style (T.filing i)).val → ζ v∈ T.notice i

lemma certified (p:BudgetPoint)(h:T.Laws ζ)(hw:A.Legal ζ): Stage.Trace.Ready (T.strand p) p ζ:= by
  constructor
  · intro i
    apply Work.H03.reads_larger (T.shifted i)
    change UsesFinal p.threshold (T.notice i) (T.reads p i); unfold reads; split
    · exact Push.Local.uses_mask _ (h.loc i)
    exact fun U W a _=> h.loc i U W a
  · intro i; change Measurable (T.reads p i); unfold reads; split
    · exact masked_measurable _ _ _ (h.Borel i)
    exact h.Borel i
  · intro i; change GaugeInvariant (T.reads p i); unfold reads; split
    · exact Push.Local.invariant_mask (h.invariant i) p.threshold _
    exact h.invariant i
  · intro i _ ha; exfalso; apply ha
    intro H; exact (A.hot (T.filing i)).ne_empty (congrArg Subtype.val H)
  intro i _ i' _ h'; exact hw (T.filing i) i' h'

section purchase
variable {f : ι→ℝ}{p:BudgetPoint} {a d:ℝ}{w:V→ℝ}

/-- Charge on every old ACTIVE placement. A uniform hit even when the
unmasked extension grows outside the good set isn't needed. -/
structure Strap (w : V→ℝ)(p:BudgetPoint)(a d:ℝ)(f:ι→ℝ): Prop where
  nonneg i : 0 ≤ f i
  here i U : ‖T.reads p i U‖ ≤ f i
  fromLabel v : SumBudget (per p.B a w (A.style ∘ T.filing) (A.region∘T.filing) f v) d

variable {ζ} [Fintype V]

lemma admission (hw : A.Legal ζ)(hW : ∀ i,0 < w i) {M : ℕ}(hO : Occupancy ζ M) (hd : 0 ≤ d)(h:T.Strap w p (a+1) d f):
    (T.strand p).Price w p.B a ((M:ℝ)*siteFactor p.B*d) f:= by
  refine ⟨h.nonneg,h.here,root_hit (mode:=fun i=> (A.style (T.filing i)).val) hO (fun i=>mul_nonneg (Poly.worth hW _).le (h.nonneg i)) hd (fun i _=>?_) ?_⟩
  · obtain ⟨v,e⟩:= A.hot (T.filing i); exact ⟨v,e,hw _ _ e⟩
  intro v
  convert h.fromLabel v using 1
  ext1 i; dsimp only [per,strand,Stage.Trace.tag,Stage.Trace.zone,plan,Function.comp_apply,expense]; split_ifs; ring; rfl
end purchase

def stated (i : ℕ)(U : Config G n): ℂ:=∑' j:Stage.Trace.sheet _ T.filing i, T.song j.val U
lemma apparent (p : BudgetPoint)(i : ℕ)(U : Config G n)(hh:Healthy p.threshold (A.region i) U):
    (T.strand p).peek i U=T.stated i U:= by
  apply tsum_congr (fun j=>?_)
  change T.reads p j.val U=T.song j.val U
  unfold reads; split
  · rw [masked_eq]; apply Finset.disjoint_of_subset_left (T.shifted j.val)
    rw [show T.filing j.val=i from j.property]; exact hh
  rfl

lemma status [Countable ι](h:T.Laws ζ)(i:ℕ):GaugeInvariant (T.stated i) ∧ Measurable (T.stated i) ∧ LocalOn ↑(A.region i) (T.stated i):= by
  haveI : Countable (Stage.Trace.sheet _ T.filing i):=by unfold Stage.Trace.sheet; infer_instance
  refine ⟨fun k U=> tsum_congr (fun j=>h.invariant j.val k U), Measurable.tsum (fun j=>h.Borel _),fun U W he=>?_⟩
  apply tsum_congr; intro j; refine h.loc _ _ _ (agrees_mono he ?_)
  exact fun _ hx=>j.property ▸ T.shifted j.val hx

end Truss

/-- The complete newly rendered signed regular error presentation. A slot
is the whole function at the prescribed group pole, not an individual
Taylor coefficient. -/
def verse : Captions R n:= ⟨A.style,A.region,fun _=>0⟩
def render (e:ℕ→Config G n→ℂ): Edition ζ R G :=⟨0,A.region,A.style,e,A.verse,fun _=>rfl⟩
def trace (p : BudgetPoint)(e:ℕ→ Config G n→ℂ): A.plan.Trace ℕ G:=⟨id,fun i=>masked p.threshold (A.region i) (e i),fun i=>A.full i⟩

variable {A ζ}
lemma credits {p:BudgetPoint} {e:ℕ→Config G n→ℂ}(h:∀i,p.Regular (A.region i) (e i))(ht:A.Legal ζ):Stage.Trace.Ready (A.trace p e) p ζ:= by
  constructor
  · exact fun i=>Push.Local.uses_mask _ (h i).sites
  · exact fun i=>masked_measurable _ _ _ (h i).borel
  · exact fun i=>Push.Local.invariant_mask (h i).symmetry _ _
  · intro i _ H; exfalso; apply H
    intro H; exact (A.hot i).ne_empty (congrArg Subtype.val H)
  intro i U x _ he; exact ht _ _ he

lemma snap {p:BudgetPoint}{e:ℕ→Config G n→ℂ} (i:ℕ) (U:Config G n):
    (A.trace p e).peek i U=masked p.threshold (A.region i) (e i) U:=by
  unfold Stage.Trace.peek
  let f : Stage.Trace.sheet _ (A.trace p e).bed i := ⟨i,rfl⟩
  rw [tsum_eq_single f (by intro j hj; exact (hj (Subtype.ext j.property)).elim)]
  rfl

variable [Fintype V]
lemma pay {p:BudgetPoint} {a d : ℝ}{w : V→ℝ}{m:ℕ→ℝ}{e:ℕ→ Config G n→ℂ} (ht:A.Legal ζ)
    (hw : ∀ i, 0 < w i) {M:ℕ}(hO:Occupancy ζ M)(hd:0≤d)
    (h : ∀ i, p.supBounds (A.post i) (A.region i) (e i) (m i))
    (hb : ∀ v, SumBudget (per p.B (a+1) w A.style A.region m v) d):
    (A.trace p e).Price w p.B a ((M:ℝ)*siteFactor p.B*d) m := by
  let T:A.Truss ℕ G:=⟨id,A.region,fun _=>true,e,fun _=>Finset.Subset.refl _⟩
  have hh:T.Strap w p (a+1) d m:= by
    refine ⟨fun i=> (h i).1,fun i U=>?_,hb⟩
    by_cases he : Healthy p.threshold (A.region i) U
    · change ‖masked _ _ _ _‖ ≤ _; rw [masked_eq _ _ _ _ he]; exact (h i).2 _ he [] (Nat.zero_le _) (by simp)
    change ‖masked _ _ _ _‖ ≤ _; rw [masked_ne _ _ _ _ he,norm_zero]; exact (h i).1
  exact T.admission ht hw hO hd hh

omit [Fintype V] in
lemma advised {p:BudgetPoint} {e:ℕ→Config G n→ℂ}(h:∀i,p.Regular (A.region i) (e i))(ht:A.Legal ζ): (A.render ζ e).Principle p := ⟨A.hot,ht,h,⟨A.hot,ht⟩⟩ -- ζ arg order?
omit [Fintype V] in
lemma insured {p:BudgetPoint}{e:ℕ→Config G n→ℂ}{a d : ℝ}{w : V→ℝ}{m:ℕ→ℝ} (hm : ∀ i,0 ≤ m i)
    (h : ∀ i,∀ x∈(A.style i).val,p.supBounds (ζ x) (A.region i) (e i) (m i))
    (hb : ∀ v, SumBudget (per p.B a w A.style A.region m v) d) : (A.render ζ e).Grant p w a 0 d 0 m:= by
  refine ⟨fun _=>by simp only [render,Pi.zero_apply,norm_zero,mul_zero]; rfl,hm,h,hb,fun i=>?_⟩
  simp [render,verse,per,expense,SumBudget]
  convert summable_zero (α:=ℝ) (β:=ℕ) using 1; ext i; simp [per,expense]
end Estate
end YM.RG3.Script
