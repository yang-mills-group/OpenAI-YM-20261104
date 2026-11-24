import YM.Integration.ActualWilsonOrdinaryCarrier
import YM.Integration.ActualWilsonRegularAdjustment

/-! A paid original Wilson regular coordinate for the complete retained ordinary
field. The residual is the actual failed-mask Taylor feed on the same carrier. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonOrdinaryChart
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Overlay Push.Local Push.AbsoluteSums
open RG3.Forms RG3.Primary Next.Foundations ActualWilsonPrimaryBudget
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

open RG3.Law RG3.Press

variable {G : Gauge} {n : Side} {V Ξ : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {o : V → Site n} {X : Rep G n} {d : ℕ} {F : Frame G d}

omit [Fintype V] in
/-- The Taylor operation changes only regular articles. The marks, radii,
forced row envelopes and captions retain their complete original bills. -/
theorem dressed {P : Rep G n} (v : V) (D : Deck B P) (A : Hol G) (sec : SectionData F) {w : ℝ}
    (he : Readable A sec P.p n w) {θ : V → ℝ} {u c fro κ reg u' c' : ℝ}
    (ha : D.Active) (hb : D.Budget θ u c fro κ reg)
    (hlog : Article.LogBounds (dress v D A sec).contents θ u' c') :
    (dress v D A sec).Active ∧ (dress v D A sec).Budget θ u' c' fro κ reg := by
  have hr := colored v D A sec he ha
  exact ⟨⟨⟨hr.rays,hr.home,hr.regular,ha.articles.occurs,ha.articles.retained,
    ha.articles.inspects,ha.articles.keeps,ha.articles.meas,ha.articles.invi⟩,ha.captions⟩,
    ⟨⟨hb.radial.pure,hlog.allowance,hb.radial.factor,hlog.bulk,hb.radial.hits⟩,hb.captions⟩⟩

/-- Native Taylor chart on W. The displayed measure of the remaining error
is an exact field, including its Wilson vacuum factor. -/
theorem chart (W : Rep G n) (T : Taste Ξ o X B) {p : BudgetPoint} {θ : V → ℝ}
    {κ reg fro : ℝ} (hw : W.p = X.p) (H : FullBudget p T θ κ reg fro)
    (x : Ξ) (v : V) (A : Hol G) (sec : SectionData F) {w : ℝ} (he : Readable A sec W.p n w)
    (ht : W.p.threshold=p.threshold) (hB : W.p.B=p.B) (ho : W.p.order≤p.order)
    (hp : W.p.power≤p.power) (hs : W.p.supportExponent+2 ≤ p.supportExponent) :
    let D := ((ActualWilsonOrdinaryCarrier.copy W T).leaf x)
    let s := (factor A sec W.p.supportExponent w * (W.p.order.factorial : ℝ)) * reg
    let c := (W.p.order.factorial : ℝ)*reg + s +
      θ v * W.p.mass (sec.footprint (D.contents.origins v)) (w*(s/θ v))
    let feed := feeds v D A sec he.sound.anchored
    ∃ q : Coefficient F n, q.Format (D.contents.origins v) A W ∧
      q.remBound (D.contents.origins v) W κ (c/θ v + fro/θ v) ∧ q.forced = 0 ∧
      (∀ U, (W.eval U : ℂ) * ((T.leaf x).log U).part (B.fire v) =
        q.density (D.contents.origins v) sec W U +
        (W.eval U : ℂ) * (feed.text U).part (B.fire v)) := by
  intro D s c feed
  let H0 := ActualWilsonOrdinaryCarrier.budget W T hw H
  have ha : D.Active := H0.active x
  have hb := ActualWilsonRegularAdjustment.deck H0 x ht hB ho hp (by linarith)
  have hstem := ActualWilsonPrimaryBudget.regular H0 A sec he ht hB ho hp hs x v
  let out := dress v D A sec
  have hlog : Article.LogBounds out.contents θ (reg+s) c :=
    hstem.log_bounds H0.radii he ha hb
  obtain ⟨hAct,hPrice⟩ := dressed v D A sec he ha hb hlog
  let t := drawer v D A sec he ha out.contents rfl rfl rfl rfl out.captions
  have hcast := t.expose hAct hPrice
  have hzero : t.index.forced = 0 := by
    rw [hcast.2]
    funext i U
    change (∑' j, if out.contents.marks i j=B.fire v then (0:ℂ) else 0) = 0
    simp
  refine ⟨t.index,t.healthy hAct,t.remit hPrice,hzero,?_⟩
  intro U
  have hz (b : Finset ℕ) : t.index.marked W b U = 0 := by
    simp [Coefficient.marked,hzero]
  have hAdjust := ActualWilsonRegularAdjustment.adjust H0 x v A sec he ht hB ho hp hs
  rw [← ActualWilsonOrdinaryCarrier.log_eq W T x (congrArg BudgetPoint.threshold hw) U]
  change _ * (D.log U).part (B.fire v) = _
  rw [hAdjust.log U,Poly.part_plus,logs v out hAct hPrice U,hcast.1 U]
  simp only [Coefficient.density,hz,tsum_zero,mul_zero,add_zero,mul_add]
  rfl

end YM.Integration.ActualWilsonOrdinaryChart
