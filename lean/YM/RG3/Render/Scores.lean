import YM.RG3.Review.Area

/-!
# Registered changes at complete receipts and price verification

API for packet/path re-alignments (and analytic short vs tail comparisons
later); can combine countably many edits at a fixed order. Footprints of
all expressions and every test variable (test supremum here used at single
argument, though equality and price at family transported separately) must
be costed before cancellation and stored as ingredient, alongside any
canonical/remainder labels. Kernel lifts which compare after translations
need to issue a certificate that works here, not equality on a per-support
old page; can use the exact restricted-domain route (per slat, FULL actual
exponent rows cancel on corresponding common mask). Does not assume equality
of density nor evaluate conditional terms under a masked identity.

Only additive edits are registered (P includes full KE/P gas; use merger
from Forms.Rewrite afterwards). For now preserve old source log/global on
the unaffected channel; or include its signed changes on a Leaf with the
complete geometry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Render
open RG RG3.Forms RG3.Press Marker Lattice Wilson Finset Function MeasureTheory Overlay Ac Push.AbsoluteSums
open Extra.Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] {R : Census V}
variable (P : Rep G n) (d : Deck R P)

/-- Entire additive formula at fixed fields. Keep path/v/signed clip
and log in same algebra. No vacuum exp expansion in comparison. Does not
include K (use density). -/
def header [Fintype V] (U : Config G n) := Poly.send R.quiet (P.exponent U) + d.log U

-- α can be large. individual pages behind a single line can be infinite
-- (sums at fixed Ui etc before translation or after flag read); every page is
-- billed at THAT expanded slat (introduce λ-dummies for unchanged infinite
-- tails instead of charging these if appropriate).
variable (G n R) (α : Type*)

structure Slat (R : Census V) (n : Side) where
  region : Support n
  pinned : region.Nonempty
  tag : R.Mode

structure Stage where
  panel : α → Slat R n

variable {G n R P d}
namespace Stage
variable {α} (t : Stage n R α) -- check Stage levels parameters order

/-- Positive ticket-vectors can be on either side. `payload` is the
*actual function contribution* of this ingredient to that log channel;
hence if masked H, include the indicator in it and only price it there.
If extracting/absorbing a global constant here, include every pertinent
signed contribution in the two Roll formulas including scalars before vs
after. Ready should be supplied without looking at other terms/totals. -/
structure Trace (I : Type*) (G : Gauge) where
  bed : I → α
  payload : I → Config G n → ℂ
  -- mention t implicit? payload & bed don't use t, include unused section through binder
  color : ∀ i : I,(t.panel (bed i)).region.Nonempty := by intro i; exact Slat.pinned ..

namespace Trace
variable {t} {I : Type*} (c : t.Trace I G)

abbrev tag (i : I) := (t.panel (c.bed i)).tag
abbrev zone (i : I) := (t.panel (c.bed i)).region

def reel (i : I) (U : Config G n) := Poly.send (c.tag i) (c.payload i U)

def tally (U) := ∑' i,c.reel i U

/-- Localized receipts before any sums. Costing supports **already in
common presentation**. Convert from shorter supports e.g. Review coupons.
Allows flags/extraTests. Includes tests evaluated on any configuration for
ingredient (don't charge just on old S if ingredient actually unmasked in
exponent). -/
structure Ready (p : BudgetPoint) (v : V → Site n) : Prop where
  read i : UsesFinal p.threshold (c.zone i) (c.payload i)
  meas i : Measurable (c.payload i)
  sym i : GaugeInvariant (c.payload i)
  fade i U : ¬ Feed.hot (c.tag i) → (c.payload i U).im=0
  root i U x : c.payload i U ≠ 0 → x∈ (c.tag i).val → v x ∈ c.zone i

structure Price (w : V → ℝ) (B : ℕ) (a δ : ℝ) (u : I → ℝ) : Prop where
  pos i : 0≤u i
  due i U : ‖c.payload i U‖ ≤ u i
  plaque : Hit c.zone B (fun i => Poly.toll w (c.tag i)*u i) a δ

def sheet (α : Type*) {I : Type*} (x : I → α) (a : α) := {i // x i=a}
instance [Countable I] (i : α) : Countable (sheet _ c.bed i) := by unfold sheet; infer_instance

def peek (i : α) (U : Config G n) := ∑' j : sheet _ c.bed i,c.payload j.val U

def cash (b : I→ℝ) (i : α) := ∑' j : sheet _ c.bed i,b j.val

lemma cash_ok (b : I→ℝ) (h : ∀ i,0 ≤ b i) (i) : 0 ≤ c.cash b i := tsum_nonneg fun i => h i.val

namespace Ready
variable {p : BudgetPoint} {c} {v : V → Site n} (H : c.Ready p v)
include H
lemma audit [Countable I] (i : α) :
    UsesFinal p.threshold (t.panel i).region (c.peek i) ∧ Measurable (c.peek i) ∧
      GaugeInvariant (c.peek i) ∧ (∀ U,¬ Feed.hot (t.panel i).tag → (c.peek i U).im=0) ∧
      (∀ U x, c.peek i U ≠ 0 → x∈ (t.panel i).tag.val → v x ∈ (t.panel i).region) := by
  let q := sheet _ c.bed i
  have he (j : q) : c.zone j.val=(t.panel i).region := congrArg (fun i => (t.panel i).region) j.property
  have ht (j:q) : c.tag j.val=(t.panel i).tag := congrArg (fun i => (t.panel i).tag) j.property
  refine ⟨fun U W ha hb => tsum_congr (fun j => (he j ▸ H.read j.val : UsesFinal p.threshold (t.panel i).region (c.payload _)) U W ha hb),
    Measurable.tsum (fun j => H.meas _), fun k U => tsum_congr (fun j => H.sym j.val k U), fun U h' => ?_,fun U x hv hx => ?_⟩
  · have hh (j : q) := H.fade j.val U ((ht j).symm ▸ h')
    -- im tsum all finite or unconditional: map with continuous linear if summable else zero.
    let f (j:q) := c.payload j.val U
    change (tsum f).im=_
    by_cases he : Summable f
    · change Complex.imCLM (tsum f)=_
      rw [Complex.imCLM.map_tsum he]
      exact (tsum_congr (fun j => hh j)).trans tsum_zero
    rw [tsum_eq_zero_of_not_summable he]; rfl
  by_contra ho; apply hv
  unfold peek
  refine (tsum_congr (g:=fun _ => 0) (fun j => ?_)).trans tsum_zero
  by_contra h'; apply ho
  rw [← he j]; exact H.root j.val U x h' (ht j ▸ hx) -- direction? need c.tag val; ht.symm ▸ hx
end Ready

namespace Price
variable {w B a δ} {c} {u : I → ℝ} (h : c.Price w B a δ u)
include h

lemma enough (hw : ∀ i,0<w i) (ha : 0≤a) : Summable u ∧ Summable (fun i => Poly.toll w (c.tag i)*u i) := by
  let f : Feed G n R I := ⟨fun i => (⟨_, Slat.pinned (t.panel (c.bed i))⟩,c.tag i),c.payload⟩
  have he : f.Worth w B a u δ := ⟨h.pos,h.due,h.plaque⟩
  exact ⟨he.enough ha hw,he.weighted_enough ha hw⟩

lemma costing (hw : ∀ i,0 < w i) (j : α) (ha : 0 ≤ a) (U) :
    ‖c.peek j U‖ ≤ c.cash u j := by
  have hp : Summable (fun i : sheet _ c.bed j => u i.val) := (h.enough hw ha).1.comp_injective Subtype.val_injective
  have ha i := h.due i U
  have he : Summable (fun i : sheet _ c.bed j => ‖c.payload i.val U‖) := hp.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ha _)
  exact (norm_tsum_le_tsum_norm he).trans (he.tsum_le_tsum (fun i => ha _) hp)

/-- aggregate all common-mask receipts. Doesn't require nonempty discrepancy at
every term; pay even matching ones if entered, so use a stationary/unaffected
log for unchanged terms on both sides (`Repair` below). -/
lemma pooled : Hit (fun i : α => (t.panel i).region) B (fun i => Poly.toll w (t.panel i).tag*c.cash u i) a δ := by
  intro x
  let f (i:I) := if x∈c.zone i then Poly.toll w (c.tag i)*u i * Real.exp (a * ↑(coverNumber B (c.zone i))) else 0
  have hf : SumBudget f δ := h.plaque x
  let g (i:α) := ∑' j : sheet _ c.bed i,f j.val
  have he : HasSum g (tsum f) := hf.2.1.hasSum.tsum_fiberwise c.bed
  convert (show SumBudget g δ from ⟨fun i => tsum_nonneg (fun j => hf.1 _),he.summable,he.tsum_eq.trans_le hf.2.2⟩) using 1
  ext i
  have h (l : sheet _ c.bed i) : c.bed l.val=i := l.property
  dsimp only [g,f,cash]
  by_cases he : x∈ (t.panel i).region
  · rw [if_pos he]; unfold zone tag; simp_rw [h,if_pos he,tsum_mul_right,tsum_mul_left]
  rw [if_neg he]; unfold zone tag; simp_rw [h,if_neg he,tsum_zero]

lemma counted (hw : ∀ i,0 < w i) (ha : 0 ≤ a) (U) :
    HasSum (fun i : α => Poly.send (t.panel i).tag (c.peek i U)) (c.tally U) := by
  have he := (Poly.budgeted hw (h.enough hw ha).2 fun i => show Poly.price w (c.reel i U) ≤ _ from by
    rw [reel,Poly.solo]; exact mul_le_mul_of_nonneg_left (h.due ..) (Poly.worth hw _).le).1
  have hh := he.hasSum.tsum_fiberwise c.bed
  apply hh.congr_fun -- name? search
  intro i
  have ht (l : sheet _ c.bed i) : (t.panel i).tag=c.tag l.val := (congrArg (fun i => (t.panel i).tag) l.property).symm
  have hy := ((h.enough hw ha).1.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => h.due i U)).of_norm.comp_injective
    (i:=fun i : sheet _ c.bed i => i.val) Subtype.val_injective
  let Q : ℂ →+ Poly R := { toFun := Poly.send (t.panel i).tag,map_add' := fun x y => by ext; simp only [Poly.part_send, Poly.part_plus]; split <;> simp, map_zero' := Poly.send_zero _ }
  have hx := (hy.hasSum.map Q (Bands.sends _)).tsum_eq
  change _ = (∑' j : sheet _ c.bed i,c.reel j.val U)
  unfold reel; simp_rw [← ht]; exact hx.symm
end Price
end Trace

/-- Two rolls of explicit signed contributions (vac, marked, scalar, regular
and path channels; no K here). Their residual at common-mask prices flows
into the merger. Keeps each in old and new support cost; can omit unchanged
lines (and needn't repurchase those) using exact algebra. -/
structure Repair (G : Gauge) (I J : Type*) where
  read : t.Trace I G
  newWay : t.Trace J G

namespace Repair
variable {t} {I J : Type*} (S : t.Repair G I J)
variable (Q : Rep G n)

def notes : Feed G n R α where
  column i := (⟨(t.panel i).region,(t.panel i).pinned⟩,(t.panel i).tag)
  value i U := S.read.peek i U-S.newWay.peek i U

def rates (u : I → ℝ) (b : J → ℝ) (i : α) := S.read.cash u i+S.newWay.cash b i

structure Local (p : BudgetPoint) (v : V→Site n) : Prop where
  before : S.read.Ready p v
  after : S.newWay.Ready p v
  -- Restricted-domain identity for old and new, not comparing gas. Can
  -- align many or condition-only participant before assembly. Combined
  -- masks avoid artifacts of late cancellations in different old labels.
  equal i U : Healthy p.threshold (t.panel i).region U → S.read.peek i U=S.newWay.peek i U

lemma lawful [Countable I] [Countable J] {p v} (h : S.Local p v) : S.notes.Keeps p v := by
  have ht := h.before.audit
  have he := h.after.audit
  refine ⟨fun i U hh => by
    change (S.read.peek i U-S.newWay.peek i U).im=_; rw [Complex.sub_im,(ht i).2.2.2.1 U hh,(he i).2.2.2.1 U hh,sub_zero],
    fun i k U => congrArg₂ (· - ·) ((ht i).2.2.1 k U) ((he i).2.2.1 k U),fun i => ((ht i).2.1).sub (he i).2.1,
    fun i U W ha hb => congrArg₂ (· - ·) ((ht i).1 U W ha hb) ((he i).1 U W ha hb), fun i U hh hx => hh (sub_eq_zero.mpr (h.equal i U hx)),
    fun i U x hh hx => ?_⟩
  by_contra hn
  apply hh
  change S.read.peek i U-S.newWay.peek i U=0
  rw [show S.read.peek i U=0 from not_ne_iff.mp (fun H => hn ((ht i).2.2.2.2 U x H hx)),
    show S.newWay.peek i U=0 from not_ne_iff.mp (fun H => hn ((he i).2.2.2.2 U x H hx)),sub_self]

lemma purchase {w : V → ℝ} {B a δ δ' u b} (hw : ∀ i,0<w i) (ha : 0 ≤ a) (h : S.read.Price w B a δ u) (h' : S.newWay.Price w B a δ' b) :
    S.notes.Worth w B a (S.rates u b) (δ+δ') := by
  classical
  refine ⟨fun i => add_nonneg (S.read.cash_ok u h.pos i) (S.newWay.cash_ok b h'.pos i),fun i U => (norm_sub_le ..).trans
    (add_le_add (h.costing hw i ha U) (h'.costing hw i ha U)),fun x => ?_⟩
  have hx := budget_plus (h.pooled x) (h'.pooled x)
  -- show equality
  refine (?_ : (fun i => if x∈ S.notes.locus i then (Poly.toll w (S.notes.mode i) * S.rates u b i) *
    Real.exp (a * coverNumber B (S.notes.locus i)) else 0) = _) ▸ hx -- direction needs symm
  funext i; dsimp only [notes,rates,Feed.mode,Feed.locus]; split_ifs <;> ring

variable [Fintype V]
end Repair
end Stage
end YM.RG3.Render
