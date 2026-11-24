import YM.Integration.ActualWilsonPrimaryBudget
import YM.Integration.ActualWilsonPrimaryPreparation

/-! Native primary adjustment of the retained physical deck with all
its regular, caption and forced entries present. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonRegularAdjustment
open Function Set Finset Lattice Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Comparison.RG02 PhysicalNext.Repeat.Legato Overlay Push.Local Push.AbsoluteSums
open RG3.Forms RG3.Primary Next.Foundations ActualWilsonPrimaryBudget
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {V Ξ : Type} [DecidableEq V] {B : Census V}
    {o : V → Site n} {P : Rep G n} {T : Taste Ξ o P B} {p : BudgetPoint}
    {θ : V → ℝ} {κ reg fro : ℝ}

private theorem reprice {ι : Type*} {q : BudgetPoint} (tag : ι → B.Mode)
    (support : ι → Support n) (v : V) {a b : ι → ℝ} {c L : ℝ}
    (hθ : ∀ j, 0 < θ j) (hp : q.B = p.B) (hs : q.supportExponent ≤ p.supportExponent)
    (hL : 0 ≤ L) (ha : ∀ j, 0 ≤ a j) (_hb : ∀ j, 0 ≤ b j)
    (hh : ∀ j, a j ≤ L*b j)
    (H : SumBudget (fun j => if v∈(tag j).val then
      Poly.toll θ (tag j)*p.mass (support j) (b j) else 0) c) :
    SumBudget (fun j => if v∈(tag j).val then
      Poly.toll θ (tag j)*q.mass (support j) (a j) else 0) (L*c) := by
  apply budget_mono (budget_scale hL H)
  · intro j
    split_ifs
    · exact mul_nonneg (Poly.worth hθ _).le (mul_nonneg (Real.exp_pos _).le (ha j))
    · rfl
  intro j
  by_cases he : v∈(tag j).val
  · rw [if_pos he,if_pos he]
    have hx : Real.exp (q.supportExponent*coverNumber q.B (support j)) ≤
        Real.exp (p.supportExponent*coverNumber p.B (support j)) := by
      rw [hp]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _))
    apply le_trans (mul_le_mul_of_nonneg_left
      (mul_le_mul hx (hh j) (ha j) (Real.exp_pos _).le) (Poly.worth hθ _).le)
    unfold BudgetPoint.mass
    ring_nf
    exact le_rfl
  · rw [if_neg he,if_neg he,mul_zero]

/-- The full native deck budget at the recipient's field and distance orders.
Every displayed cost comes from the original per-mark regular or forced bill. -/
theorem deck (H : FullBudget p T θ κ reg fro) (x : Ξ)
    (ht : P.p.threshold=p.threshold) (hB : P.p.B=p.B)
    (ho : P.p.order≤p.order) (hp : P.p.power≤p.power)
    (hs : P.p.supportExponent≤p.supportExponent) :
    (T.leaf x).Budget θ reg ((P.p.order.factorial : ℝ)*reg) fro κ reg := by
  let L := (P.p.order.factorial : ℝ)
  have hL : 0 ≤ L := by positivity
  have split (v : V) := H.regularTotal v
  refine ⟨⟨H.radii, ?_, H.divisor, ?_, ?_⟩, ⟨?_⟩⟩
  · intro v
    obtain ⟨b,c,hb,hc,hcost⟩ := split v
    apply le_trans (mul_le_mul_of_nonneg_left (H.unit x v) (H.radii v).le)
    linarith [budget_nonneg hb,budget_nonneg hc]
  · refine ⟨fun j => L*H.white j, fun j => ⟨mul_nonneg hL (H.white_nonnegative j),?_⟩,?_⟩
    · intro v hv
      change P.p.supBounds (T.menu.origins v) _ _
        ((P.p.order.factorial : ℝ)*H.white j)
      rw [T.root]
      exact native_derivatives ((H.regular j).controls x v hv) ht ho hp
    intro v
    obtain ⟨b,c,hb,hc,hcost⟩ := split v
    have hunit := mul_nonneg (H.radii v).le (H.unit_nonnegative v)
    have hpaid : b ≤ reg := by linarith [budget_nonneg hc]
    exact reprice T.menu.rays T.menu.branch v H.radii hB hs hL
      (fun j => mul_nonneg hL (H.white_nonnegative j)) H.white_nonnegative
      (fun _ => le_rfl) (budget_loosen hb hpaid)
  · refine ⟨H.black,fun i j => ⟨H.black_nonnegative (i,j),H.forced x i j⟩,?_⟩
    intro v
    have h := reprice (fun j : ℕ × ℕ => T.menu.marks j.1 j.2)
      (fun j => (P.activities.forced j.1).support) v H.radii hB hs zero_le_one
      H.black_nonnegative H.black_nonnegative (fun j => (one_mul _).symm.le) (H.forcedTotal v)
    rw [one_mul,mul_comm κ fro] at h
    convert h using 1
    funext j
    change (if v∈(T.menu.marks j.1 j.2).val then _ else _) =
      (if v∈(T.menu.marks j.1 j.2).val then _ else _)
    split_ifs <;> rfl
  intro v
  obtain ⟨b,c,hb,hc,hcost⟩ := split v
  have hunit := mul_nonneg (H.radii v).le (H.unit_nonnegative v)
  have hpaid : c ≤ reg := by linarith [budget_nonneg hb]
  have h := reprice T.tag T.site v H.radii hB hs zero_le_one
    (fun j => norm_nonneg (T.score x j)) H.gold_nonnegative
    (fun j => (H.caption x j).trans_eq (one_mul _).symm) (budget_loosen hc hpaid)
  rw [one_mul] at h
  convert h using 1
  funext j
  change (if v∈(T.tag j).val then _ else _) = (if v∈(T.tag j).val then _ else _)
  split_ifs <;> rfl

variable [Fintype V] {d : ℕ} {F : Frame G d}

/-- Actual operation of the native extractor on the same full signed leaf. -/
theorem adjust (H : FullBudget p T θ κ reg fro) (x : Ξ) (v : V)
    (A : Hol G) (sec : SectionData F) {w : ℝ} (he : Readable A sec P.p n w)
    (ht : P.p.threshold=p.threshold) (hB : P.p.B=p.B)
    (ho : P.p.order≤p.order) (hp : P.p.power≤p.power)
    (hs : P.p.supportExponent+2 ≤ p.supportExponent) :
    Adjust (T.leaf x) (feeds v (T.leaf x) A sec he.sound.anchored) P
      (dress v (T.leaf x) A sec) :=
  funded v (T.leaf x) A sec he (H.active x) (deck H x ht hB ho hp (by linarith))
    (regular H A sec he ht hB ho hp hs x v)


/-- On the actual retained regulator the regular Taylor adjustment is
constructed at the literal normalized residual leaf. Every new term and
the adjusted deck use the same native output representative and root. -/
theorem selected (R : Run G)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F}
    (S : Chosen K I M) {δ : ℝ} {a : ℕ} (H : Bounds S δ a)
    (x : IndependentTests J.tests) (v : V)
    (href : R.family.ref (J.outputWeight v) ≤ datum.level)
    (hord : (R.family.path.levels.budget datum.level).order ≤ J.outputFieldOrder)
    (hdist : (R.family.path.levels.budget datum.level).power ≤ J.outputDistanceOrder)
    (hres : (R.family.path.levels.budget datum.level).supportExponent+2 ≤ J.outputSupport) :
    let C := R.family
    let X := S.output.carrier.rep
    let sec := C.localSection (J.outputWeight v)
    let cost := envelopeProduct (R := B) F.kernelCosts
    let D := (priceNormalized cost (pullback (testInclusion J.tests) S.output.residual)).leaf x
    let he := ActualWilsonPrimaryPreparation.selected R (J.outputWeight v) S href
    Adjust D (feeds v D C.params sec he.sound.anchored) X (dress v D C.params sec) := by
  intro C X sec cost D he
  let i := datum.level
  have h0 : X.p = C.path.levels.budget i := S.output.carrier.point
  have hl := A.output_norm i
  apply adjust H.residual_price.budget x v C.params sec he
  · exact (congrArg BudgetPoint.threshold h0).trans hl.threshold.symm
  · exact (congrArg BudgetPoint.B h0).trans hl.block.symm
  · rw [h0,hl.order]
    exact hord
  · rw [h0,hl.distance]
    exact hdist
  · rw [h0,hl.reserve]
    exact hres

end YM.Integration.ActualWilsonRegularAdjustment
