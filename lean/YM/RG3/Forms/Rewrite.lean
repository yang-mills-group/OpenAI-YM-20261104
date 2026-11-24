import YM.RG3.Forms.Partners
import YM.RG3.Forms.Accounts
/-!
# Exact complete density and attachment budget transport, Common producer

Re-expression **after** inherited and analytic terms have been supplied or
compared as real densities, at arbitrary order of that comparison and finite
orders of weighted derivatives at P. Path terms and unmarked/contact resets
may differ between P and Q, and regular layout/output bound supplied; in
particular clipping/cone channels need their actual discrepancies included
and no assertion that K or global mass follows from equality. No equality
premise on polynomial density; two additive common-mask receipts accounting
for all changes (components will discharge for masks, some path/packet and
stencil changes), positive input-price receipts at the stated reserves from
suppliers, assembly produces the complete point identity plus the forced
part of the represented-error estimate. Keep both unmarked scalar and gas,
and every mandatory failed-mask contribution. Need same budget point for the
operation; using with numbers from another level without gate invalid.

Legitimate re-expression of even the vacuum on its same witness (not issued
as NEW Wilson selection; caller proves push transports etc using `actual
transfer`). Alternative pure-move interface fixed P is usually used with
normalized RG comparison; no extra unmarked representation cost needed.
Canonical coordinates as H/units/global plus residual paths separately priced
before this theorem: e.g. p.mass c still includes cover and sup weighted
left derivatives; using remBound consumer additionally requires projection
nulls, a stronger premise/special construction. Does not assert
coupling or field-coordinate remBound estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Forms
open RG3.Ink RG3.Press Marker Lattice Wilson RG Function MeasureTheory Ac Overlay Extra.Trajectories Finset Push.Corrected Push.AbsoluteSums
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] [Fintype V] {R : Census V}
variable {P : Rep G n} (input : Deck R P) {I : Type*} (f : Feed G n R I)

-- specify Output REGULAR data including scalar. K and T.entries on `out`
-- dummy/ignored; fill here.
structure Adjust (Q : Rep G n) (o : Deck R Q) : Prop where
  clock : P.p=Q.p
  compatible : input.contents.origins = o.contents.origins
  vacuum U : P.exponent U = Q.exponent U + f.bare U
  log U : input.log U = o.log U + f.text U

abbrev catalog : Shelf G n ℕ (Column R n) := ⟨P.activities.forced, Feed.region, fun c => c.1.property⟩

section Printer
variable (s : ℝ) (w : V → ℝ) (vac mark : ℝ)
local notation "κ" => (P.p.supportExponent+1)
structure Test extends Billboard input.contents w P.p.B κ vac mark where
   radii i : 0 < w i
   articles : input.contents.Active
   check : P.activities.ForcedFamily P.p
   slip : f.Keeps P.p input.contents.origins
   cents : I → ℝ
   budget : f.Worth w P.p.B κ cents s
   sufficesStamp : s ≤ 1

namespace Test
variable {s w vac mark input f} (k : Test input f s w vac mark)

def stock [Countable I] : catalog (P:=P) (R:=R)|>.Stock P.p R input.contents.origins := {
  hardVal := input.contents.each
  slipVal := f.slip
  hardLocal := k.toBillboard.locality k.radii (by have := P.p.exponent_pos; linarith) k.articles k.check
  hardCharged := Billboard.asserts k.articles k.check
  slipLocal := f.used k.slip
  flagged := f.profits k.slip }

-- types infer?
def coins : (ℕ ⊕ Column R n) → Poly R := Sum.elim k.toBillboard.merch (f.coin k.cents)

local notation "uni" => catalog (P:=P) (R:=R)
-- countable letters remain in the view
local instance {ι μ : Type*} [Countable ι] [Countable μ] (D : Shelf G n ι μ) : Countable D.Patch := by unfold Shelf.Patch Letters.Frame.Patch; infer_instance

include k
omit [Fintype V] in
lemma offer (χ γ : ℝ) (hc : 1 ≤ χ) (h : χ*(vac+mark)+2*s ≤ γ) :
    Hit (uni).frame.read P.p.B ((uni).frame.pump (fun i => Poly.price w (k.coins i)) χ) κ γ := by
  have ha := (show 0 ≤ κ by have := P.p.exponent_pos; linarith)
  have hs := f.payment k.radii ha k.budget
  have hh := k.toBillboard.purchase k.radii ha
  intro x
  refine budget_of_sum (fun i => ?_) (fun u => le_trans ?_ h)
  · split
    · refine mul_nonneg (show 0 ≤ (uni).frame.pump _ χ i from ?_) (Real.exp_pos _).le
      rcases i with i|i
      · unfold Letters.Frame.pump; rw [if_pos ((uni).inl_hard i)]
        exact mul_nonneg (zero_le_one.trans hc) (Poly.nonnegative k.radii _)
      unfold Letters.Frame.pump; rw [if_neg ((uni).inr_hard i)]; exact Poly.nonnegative k.radii _
    exact le_rfl
  rw [sum_sum_eq_sum_toLeft_add_sum_toRight]
  refine add_le_add ?_ (le_trans ?_ (budget_sum (hs x) u.toRight))
  · refine le_trans ?_ (budget_sum (budget_scale (x:=χ) (by linarith) (hh x)) u.toLeft)
    refine sum_le_sum (fun i _ => ?_)
    simp only [Letters.Frame.pump, Shelf.inl_hard, ↓reduceIte]
    change (if x∈ (P.activities.forced i).support then _ else _) ≤ χ*(if x ∈ _ then _ else _)
    split <;> simp [coins,mul_assoc,Shelf.frame]
  refine sum_le_sum (fun i _ => ?_)
  simp only [Letters.Frame.pump, Shelf.inr_hard, ↓reduceIte]; exact le_rfl

variable [Countable I]
omit [Fintype V] in
lemma service (χ γ : ℝ) (hχ : 1 ≤ χ) (h : χ*(vac+mark)+2*s ≤ γ) (hγ : 0≤γ)
    (green : (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) :
    (stamp k.stock).Sound ∧ (stamp k.stock).Budget w ((Real.exp γ-1)/χ) ∧
    ∀ U, input.contents.cluster U * (∏ i : Column R n,(1+f.slip i U)) = (stamp k.stock).cluster U := by
  have ha := (show 0≤κ by have := P.p.exponent_pos; linarith)
  obtain ⟨HB,hC,hL,hR,hH⟩ := k.stock.fiscally k.radii (g:=k.coins) (fun i U => show Width.Covered _ _ from by
    rcases i with i|i
    · exact (k.toBillboard.qual k.radii ha i U).receipts
    exact f.funded k.radii ha k.sufficesStamp k.budget i U)
    P.p.exponent_pos.le hχ hγ (k.offer χ γ hχ h) green
  refine ⟨stamped k.stock k.check.meas_test k.check.symtest k.check.reads_test (fun i U => ?_), ⟨_,hC,hH⟩,fun U => ?_⟩
  · rcases i with i|i
    · exact (k.toBillboard.silent k.radii ha k.articles i U) ▸ Complex.ofReal_im _
    exact f.admitted i U
  · have HE b : k.stock.tray U b=input.contents.packet b U := by
      classical
      unfold Shelf.Stock.tray Bands.packet Activities.admissible
      split <;> rename_i hs
      · split
        · rfl
        next hh => exact (hh hs).elim
      split
      next hh => exact (hs hh).elim
      rfl
    simp_rw [stamp_cluster,Bands.cluster,← HE] -- HE rewrites packet (need cluster unfold)
    exact (HB U).2.2


-- after replacing K, retain every outgoing regular channel including mask support,
-- also when replacing vacuum dictionary. Allows further adapters to imitation
-- `P.p` inclusion. `Repression` agrees on p & origin but doesn't require all K tests
-- covered by d.flow (provide separately).
def task (h : Accessible P) (o : Deck R P) [Nonempty V] : Deck R P := {
    contents := (stamp k.stock).impression o.contents (wharf (p:=P.p) P h)
    captions := o.captions }

def push (Q : Rep G n) := (stamp k.stock).ledger Q

def align (Q : Rep G n) (o : Deck R Q) : Bands R (k.push Q) :=
    ⟨o.contents.origins,o.contents.units,o.contents.support,o.contents.rays,o.contents.H,o.contents.marks,o.contents.entries⟩

def layout (Q : Rep G n) (o : Deck R Q) [Nonempty V] : Deck R (k.push Q) := {
    contents := (stamp k.stock).impression (k.align Q o) pin
    captions := o.captions }

theorem exponent_push (Q : Rep G n) : (k.push Q).exponent=Q.exponent := rfl

-- use actual law already supplied as input. Environments for unmarked or
-- for marked summability with larger budgets export later.
lemma answer {Q : Rep G n} {o : Deck R Q} (ho : Adjust input f Q o) (H : ∀ U, (stamp k.stock).cluster U=input.contents.cluster U*(∏ i : Column R n,(1+f.slip i U)))
    (out : Deck R (k.push Q)) (he : out.log=o.log) (hn : out.contents.cluster=(stamp k.stock).cluster)
    {Θ δ c d b a} (hb : input.Budget Θ δ c d b a) (hA : input.Active) (U) :
    out.density U=input.density U := by
  have ha := (show 0≤κ by have := P.p.exponent_pos; linarith)
  have hh := f.combine U k.radii ha k.budget
  have ht := f.bare U
  have hy := f.text U
  have hX : (o.log U).part R.quiet=0 := by
    have hl := input.quiet hA hb U; rw [ho.log U,Poly.part_plus,k.budget.quiet_text ha k.radii U,add_zero] at hl; exact hl
  unfold Deck.density
  rw [he,hn,H,ho.log U,←hh, ← Poly.product_bead, ← Poly.product_bead,exponent_push, ho.vacuum U,Real.exp_add,Complex.ofReal_mul,map_mul,pass_add hX (k.budget.quiet_text ha k.radii _)]
  ac_rfl

variable [Nonempty V]

/-- The simultaneous re-expression producer interface. At each point of
same fixed regulator and masks. Output Rep has dummy K replaced by our
exact patches at cost across actual configuration space, with output δW etc
usually chosen at the public thresholds *after* the operation; also
outputs a same-census marked presentation with all references unchanged
and compatible with Overlay data (captions optional). Exact recovery also
for the unmarked density, hence e.g. its partition/Haar environment may be
reused with that of the fixed witness. Input marked source needn't be
calibrated. Does not assert insertion push or smooth/conditional denom
beyond admitted inputs (but enables a transitive adapter when supplied an
identity or estimate on those same Decks). `v` path gauge scalar may differ
on `Q`.

What caller must do for paths: register actual discrepancies separated with
an actual flag for every different mask even on a nonzero re-rendered
remainder, enforce exact identities only at regular level (incl scalar) on
same U, purchase their support and kernel costs before any counted slip.
Supply the new path/regular presentation laws as well as its regular norm;
these are a distinct problem from the *cost of the representation change*
here for forces. Use mask and render interfaces later to obtain them. -/
theorem produce (χ γ : ℝ) (hχ : 1 ≤ χ) (h : χ*(vac+mark)+2*s ≤ γ) (hγ : 0≤γ)
    (green : (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) {Q : Rep G n} {o : Deck R Q} (ho : Adjust input f Q o)
    {σi Ci Λi δi Wi Θ δ c d b a}
    (hI : P.Lawful σi Ci Λi δi Wi) (hb : input.Budget Θ δ c d b a) (hA : input.Active)
    {σ C Λ η W δ' c' d' b' a' : ℝ}
    (hv : (Real.exp γ-1)/χ ≤ W) (hp : Q.path.Bounds Q.clip σ C Λ)
    (hm : ∀ s b, Nonempty (Q.activities.Moves s b)) (hE : Q.activities.RegularFamily Q.p) (hη : Q.activities.EBound Q.p η)
    (HE : ∀ s b, Nonempty ((stamp k.stock).Spin s b)) (Hδ : (Real.exp γ-1)/χ ≤ d'*b') (Hb : 0<b')
    (HT : Article.Contents o.contents) (HX : Article.LogBounds o.contents w δ' c')
    (HC : o.captions.Sound o.contents.origins) (Hy : o.captions.Paid w Q.p a') :
    let out := k.layout Q o
    let Qout := k.push Q
    out.Active ∧ out.Budget w δ' c' d' b' a' ∧ out.density=input.density ∧
      Qout.Lawful σ C Λ η W ∧ Qout.eval=P.eval := by
  intro out Qout
  obtain ⟨HD,hB,hh⟩ := k.service χ γ hχ h hγ green
  have hs : Qout.Lawful σ C Λ η W :=
    (stamp k.stock).lawful Q ho.clock.symm HD k.radii hB hv hp hE hη hm HE
  obtain ⟨Ha,Hc,hCluster⟩ := (stamp k.stock).publish (k.align Q o) pin ((stamp k.stock).ledger_host Q ho.clock.symm HD)
    ho.compatible HD (show Article.Contents (k.align Q o) from ⟨HT.rays, HT.home, HT.regular⟩)
    (show Article.LogBounds (k.align Q o) w δ' c' from ⟨HX.allowance,HX.bulk⟩) k.radii hB Hb Hδ ((stamp k.stock).ledger_q Q HD)
  have h' := funext (k.answer ho (fun U => (hh U).symm) out rfl hCluster hb hA)
  have HA : out.Active := ⟨Ha,HC⟩
  have H' : out.Budget w δ' c' d' b' a' := ⟨Hc,Hy⟩
  refine ⟨HA,H',h',hs,funext fun U => Complex.ofReal_injective ?_⟩
  rw [← input.vacuum hA hb hI.labels U,← out.vacuum HA H' hs.labels U,h']

/-- Pure marked route: exact on fixed P. No symmetry supply for marked rows
or receipt (! invariance under pull still comes from pointwise density
identity on both rotated configurations, if supplied on input). Extra tests
may be stricter than aperture. The auxiliary common change data asks for
alignment including vacuum/additive costs but here those remain P all along.
Needn't call `service` on unmarked coefficients at this exact application if
using an additional marked-only reserve argument. Here still paying hh hit
for BOTH in merger, expose prominently as reserve requirement. -/
theorem stay (χ γ : ℝ) (hχ : 1 ≤ χ) (h : χ*(vac+mark)+2*s ≤ γ) (hγ : 0≤γ)
    (green : (P.p.B+P.p.B+1:ℕ)^4*(γ:ℝ) ≤ 1) (HA : Accessible P) {o : Deck R P} (ho : Adjust input f P o)
    (hs0 : ∀ i U, (f.slip i U).part R.quiet=0)
    {Θ δ c d b a} (hb : input.Budget Θ δ c d b a) (hA : input.Active)
    {δ' c' d' b' a' : ℝ} (Hδ : (Real.exp γ-1)/χ ≤ d'*b') (Hb : 0<b')
    (HT : Article.Contents o.contents) (HX : Article.LogBounds o.contents w δ' c')
    (HC : o.captions.Sound o.contents.origins) (Hy : o.captions.Paid w P.p a') :
    let out := k.task HA o
    out.Active ∧ out.Budget w δ' c' d' b' a' ∧ out.density=input.density := by
  intro out
  obtain ⟨HD,hB,hComm⟩ := k.service χ γ hχ h hγ green
  have ha := (show 0≤κ by have := P.p.exponent_pos; linarith)
  obtain ⟨HAct,Hc,hCluster⟩ := (stamp k.stock).publish o.contents (wharf (p:=P.p) P HA)
    (wharf_fit P k.stock HA rfl rfl) ho.compatible HD HT HX k.radii hB Hb Hδ (wharf_eq P k.stock HA hs0 (k.toBillboard.silent k.radii ha hA.articles))
  let substitute : Deck R (k.push P) := ⟨k.align P out,out.captions⟩
  -- cannot use hCluster for substitute.cluster because P.K and push P have different K!
  refine ⟨⟨HAct,HC⟩,⟨Hc,Hy⟩,funext fun U => ?_⟩
  have hh := f.combine U k.radii ha k.budget
  have hX : (o.log U).part R.quiet=0 := by
    have hl := input.quiet hA hb U; rw [ho.log U,Poly.part_plus,k.budget.quiet_text ha k.radii U,add_zero] at hl; exact hl
  unfold Deck.density
  have h0 : out.log U=o.log U := rfl
  have hK : out.contents.cluster U=_ := congrFun hCluster U
  rw [h0,hK,← hComm U,ho.log U,←hh, pass_add hX (k.budget.quiet_text ha k.radii _)]
  have he : f.bare U=0 := by linarith only [ho.vacuum U]
  rw [he,Real.exp_zero,Complex.ofReal_one,map_one,one_mul]
  congr 1
  ac_rfl

end Test
end Printer
end YM.RG3.Forms
