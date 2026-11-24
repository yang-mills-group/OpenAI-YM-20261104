import YM.Integration.WilsonMarkedRegularReserve
import YM.Integration.WilsonRegularDrawer
import YM.Integration.ActualWilsonOrdinaryChart

/-! The measured coefficient and signed Taylor feed of one actual marked
regular residual on the same original gallery. The finite auxiliary hard
price cancels from each of its uniform regular and measured bills. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredMarkedPrimary
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison Overlay Push.Local Push.AbsoluteSums RG3.Forms RG3.Primary
open RG3.Law RG3.Press QuadraticLocal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V T ι : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    [Nonempty T] [Countable ι] {B : Census V} {o : V → Site n} {W : Rep G n}
    {d : ℕ} {F : Frame G d}

private theorem size_unit (F:Frame G d) (a:ℂ) (y:F.Coeff) :
    F.coeffSize (a • F.e0+y) ≤ ‖a‖+F.coeffSize y := by
  unfold Frame.coeffSize
  calc
    _ ≤ ∑ i, (‖(a • F.e0) i‖+‖y i‖) := Finset.sum_le_sum (fun i _ => norm_add_le _ _)
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_eq_single 0]
      · simp [Frame.e0]
      · intro i _ hi
        simp [Frame.e0,hi]
      · simp

theorem posted (L : Gallery T ι o W B) {θ : V → ℝ} {κ reg hard : ℝ}
    (hw : ∀v,0<θ v) (divisor:0<κ) (valid:W.activities.ForcedFamily W.p)
    (regular:L.E.Paid θ W.p.B (W.p.supportExponent+2) reg)
    (forced:L.K.Paid θ W.p.B W.p.supportExponent hard)
    (x : T) (v : V) (A : Hol G) (sec : SectionData F) {w : ℝ} (he : Readable A sec W.p n w) :
    let D := (ActualWilsonOrdinaryCarrier.copy W (Display.taste L)).leaf x
    let r := 4*reg
    let s := (factor A sec W.p.supportExponent w * (W.p.order.factorial : ℝ)) * r
    let c := (W.p.order.factorial : ℝ)*r + s + θ v*W.p.mass (sec.footprint (o v)) (w*(s/θ v))
    let feed := feeds v D A sec he.sound.anchored
    ∃ q:Coefficient F n,q.Format (o v) A W ∧ q.remBound (o v) W κ (c/θ v) ∧ q.forced=0 ∧
      θ v*F.coeffSize q.x ≤ 2*(r+s) ∧
      (∀ U,(W.eval U:ℂ)*(L.E.log x U).part (B.fire v) =
        q.density (o v) sec W U + (W.eval U:ℂ)*(feed.text U).part (B.fire v)) ∧
      ∀ U,flags W.p.threshold U=∅ →
        (W.eval U:ℂ)*(L.E.log x U).part (B.fire v)=q.density (o v) sec W U := by
  intro D r s c feed
  obtain ⟨aux,⟨H⟩⟩:=WilsonMarkedRegularReserve.original L hw divisor valid regular forced
  let H0 := ActualWilsonOrdinaryCarrier.budget W (Display.taste L) rfl H
  have ha : D.Active:=H0.active x
  have hb:=ActualWilsonRegularAdjustment.deck H0 x rfl rfl le_rfl le_rfl
    (show W.p.supportExponent≤(WilsonMarkedRegularReserve.raised W.p).supportExponent by
      change W.p.supportExponent ≤ W.p.supportExponent+2; linarith)
  have hstem:=ActualWilsonPrimaryBudget.regular H0 A sec he rfl rfl le_rfl le_rfl le_rfl x v
  have root : D.contents.origins v=o v:=congrFun (ActualWilsonOrdinaryCarrier.copy W (Display.taste L)).root v
  let out:=dress v D A sec
  have hlog : Article.LogBounds out.contents θ (r+s) c := by
    have h:=hstem.log_bounds H0.radii he ha hb
    change Article.LogBounds out.contents θ (r+s)
      ((W.p.order.factorial:ℝ)*r+s+θ v*W.p.mass (sec.footprint (D.contents.origins v)) (w*(s/θ v))) at h
    rw [root] at h
    exact h
  obtain ⟨hAct,hPrice⟩ := ActualWilsonOrdinaryChart.dressed v D A sec he ha hb hlog
  let t := drawer v D A sec he ha out.contents rfl rfl rfl rfl out.captions
  have hcast := t.expose hAct hPrice
  have hzero : t.index.forced = 0 := by
    rw [hcast.2]
    funext i U
    change (∑' j, if out.contents.marks i j=B.fire v then (0:ℂ) else 0) = 0
    simp
  let co:=RG3.Primary.comp v D A F
  have unit := RG3.Primary.name_income v out hAct hPrice
  have core : F.coeffSize (F.core co) ≤ s/(θ v) :=
    (Work.G08.size_core F co).trans (hstem.combine H0.radii he ha).2
  have linear : θ v * F.coeffSize t.index.x ≤ 2*(r+s) := by
    change θ v * F.coeffSize (legend v out • F.e0+F.core co) ≤ _
    have triangle := size_unit F (legend v out) (F.core co)
    apply (mul_le_mul_of_nonneg_left triangle (H.radii v).le).trans
    rw [mul_add]
    have used:=mul_le_mul_of_nonneg_left core (H.radii v).le
    have cancel : θ v*(s/θ v)=s := by field_simp [(H.radii v).ne']
    rw [cancel] at used
    linarith
  have exact_field U : (W.eval U:ℂ)*(L.E.log x U).part (B.fire v) =
      t.index.density (o v) sec W U+(W.eval U:ℂ)*(feed.text U).part (B.fire v) := by
    have hz (b:Finset ℕ) : t.index.marked W b U=0 := by simp [Coefficient.marked,hzero]
    have adjust:=ActualWilsonRegularAdjustment.adjust H0 x v A sec he rfl rfl le_rfl le_rfl le_rfl
    have old:=Display.tasteH L x U hw (Lamps.tenure _ _ hw regular (by linarith))
    rw [←old,←root,←ActualWilsonOrdinaryCarrier.log_eq W (Display.taste L) x rfl U]
    change _*(D.log U).part (B.fire v)=_
    rw [adjust.log U,Poly.part_plus,logs v out hAct hPrice U,hcast.1 U]
    simp only [Coefficient.density,hz,tsum_zero,mul_zero,add_zero,mul_add]
    rfl
  refine ⟨t.index,root ▸ t.healthy hAct,root ▸ WilsonRegularDrawer.price t hPrice hzero,hzero,
    linear,exact_field,?_⟩
  intro U hU
  have kept:=RG3.Primary.kept v D A sec he ha
  have clear i : feed.value i U=0 := by
    by_contra h
    exact kept.flags i U h (by simp [Healthy,hU])
  have gone : feed.text U=0 := by simp [Feed.text,clear]
  simpa [gone] using exact_field U
end YM.Integration.WilsonMeasuredMarkedPrimary
