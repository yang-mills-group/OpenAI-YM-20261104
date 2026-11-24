import YM.Integration.ActualWilsonOrdinaryChart
import YM.Integration.ActualWilsonSpectatorBudget

/-! The original anchored sum of the failed-mask Taylor fields and the
compulsory-coverage price of the scalar vacuum factor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonFailedMaskPrice
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Marker Source Labels
open Extra.Histories RG3.Forms RG3.Primary RG3.Press Push.Local Push.AbsoluteSums
open Overlay SectorNext.Vacuum CoveredOrdinaryMinor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

theorem vacuum {P : Rep G n} {p : BudgetPoint} {w : ℝ} (hP : P.activities.KBound p w)
    (hw : w ≤ 1) (U : Config G n) :
    ‖P.activities.gas P.p U‖ ≤ if flags P.p.threshold U = ∅ then 1 else w := by
  obtain ⟨b,hb,hpay⟩ := hP
  let K (j : ℕ) := (P.activities.forced j).support
  let Z (j : ℕ) := (P.activities.forced j).inventory
  let D := flags P.p.threshold U
  have hit (x : Site n) (I : Finset ℕ) : (∑ j ∈ I, if x ∈ Z j then b j else 0) ≤ w := by
    apply le_trans _ (budget_sum (hpay x) I)
    apply Finset.sum_le_sum
    intro j _
    by_cases hz : x ∈ Z j
    · rw [if_pos hz,if_pos ((P.activities.forced j).inventory_sup hz)]
      exact p.loMass _ _ (hb j).1
    rw [if_neg hz]
    split
    · exact (hb j).1.trans (p.loMass _ _ (hb j).1)
    exact le_rfl
  have H := covered_budget K Z (γ := 0) (fun j => (P.activities.forced j).inventory_sup)
    (fun j => (P.activities.forced j).inventory_ne) hw b (fun j => (hb j).1)
    (fun x I => by simpa only [zero_mul,Real.exp_zero,mul_one] using hit x I) D
  simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at H
  have hs : SumBudget (fun s : Finset ℕ => ‖P.activities.gasOccurrence P.p s U‖)
      (if D=∅ then 1 else w) := by
    apply budget_mono H (fun _ => norm_nonneg _)
    intro s
    have hA : accounted K Z D s ↔ P.activities.admissible P.p U s := by
      apply iff_of_eq
      unfold accounted Activities.admissible K Z D
      congr!
    by_cases hh : P.activities.admissible P.p U s
    · simp only [Activities.gasOccurrence,hh,if_true,hA,norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun j _ => (hb j).2 U)
    · simp [Activities.gasOccurrence,hh,hA]
  exact (norm_tsum_le_tsum_norm hs.2.1).trans hs.2.2

variable {V : Type} [DecidableEq V] {B : Census V}
    {d : ℕ} {F : Frame G d} {P : Rep G n}

theorem feed (v : V) (D : Deck B P) (A : Hol G) (sec : SectionData F)
    {w : ℝ} (he : Readable A sec P.p n w) (ha : D.Active) {θ : V → ℝ}
    {m : ℕ → ℝ} {s : ℝ} (hθ : ∀ v, 0 < θ v) (H : StemPay v D A sec w θ m s) :
    let T := feeds v D A sec he.sound.anchored
    let f := fun U => (T.text U).part (B.fire v)
    Measurable f ∧ GaugeInvariant f ∧
      (∀ U, flags P.p.threshold U=∅ → f U=0) ∧ ∀ U, ‖f U‖ ≤ s/θ v := by
  intro T f
  have hk := kept v D A sec he ha
  have stock := H.stock hθ he
  have hp := H.purchase hθ he ha
  have heq (U) : f U = ∑' j, T.value j U := by
    have hs : Summable (fun j => Poly.send (B.fire v) (T.value j U)) :=
      (Poly.budgeted (fun _ => zero_lt_one) stock.2.1 (fun j => by
        rw [Poly.solo,Poly.solo_toll,one_mul]
        exact hp.always j U)).1
    have htext : T.text U = ∑' j, Poly.send (B.fire v) (T.value j U) := by
      apply tsum_congr
      intro j
      change (if Feed.hot (B.fire v) then Poly.send (B.fire v) (T.value j U) else 0) = _
      rw [if_pos (show Feed.hot (B.fire v) from B.fire_hot v)]
    change (T.text U).part (B.fire v) = _
    rw [htext,Poly.share hs]
    simp only [Poly.part_send,if_true]
  refine ⟨?_,?_,?_,?_⟩
  · rw [show f = fun U => ∑' j, T.value j U from funext heq]
    exact Measurable.tsum fun j => hk.borel j
  · intro g U
    rw [heq,heq]
    exact tsum_congr (fun j => hk.gauge j g U)
  · intro U h
    rw [heq]
    apply (tsum_congr (g := fun _ : ℕ => (0:ℂ)) ?_).trans tsum_zero
    intro j
    by_contra hn
    exact (hk.flags j U hn) (by simp [Healthy,h])
  · intro U
    rw [heq]
    have hn := stock.2.1.of_nonneg_of_le (fun j => norm_nonneg (T.value j U)) (fun j => hp.always j U)
    exact (norm_tsum_le_tsum_norm hn).trans ((Summable.tsum_le_tsum (fun j => hp.always j U)
      hn stock.2.1).trans stock.2.2)

/-- Every failed-mask contribution is on a dirty configuration, so its
reweighted original vacuum pays the small forced allowance there. -/
theorem reweighted {w M : ℝ} {p : BudgetPoint} (hP : P.activities.KBound p w) (hw : w ≤ 1)
    (hw0 : 0 ≤ w) (f : Config G n → ℂ) (hf : ∀ U, ‖f U‖ ≤ M)
    (hclean : ∀ U, flags P.p.threshold U=∅ → f U=0) (U : Config G n) :
    ‖(P.activities.gas P.p U : ℂ)*f U‖ ≤ w*M := by
  by_cases h : flags P.p.threshold U = ∅
  · rw [hclean U h,mul_zero,norm_zero]
    exact mul_nonneg hw0 ((norm_nonneg _).trans (hf U))
  · have hg := vacuum hP hw U
    rw [if_neg h] at hg
    rw [norm_mul,Complex.norm_real]
    exact mul_le_mul hg (hf U) (norm_nonneg _) hw0

end YM.Integration.ActualWilsonFailedMaskPrice
