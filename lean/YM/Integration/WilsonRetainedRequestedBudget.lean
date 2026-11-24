import YM.Integration.WilsonRetainedPointBudget
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Integration.LocalComparisonEnvelope

/-! The genuine pretest receipt at the requested analytic input norm, with unchanged wallets. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonRetainedRequestedBudget

open Finset Lattice Wilson RG Marker Overlay Push.AbsoluteSums RG3.Script.Picnic LocalComparison
open ComparisonDensity.Address Extra.Iteration.Comparison
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} {n : Side} {V X : Type} [Fintype V] [DecidableEq V]
  {R : Census V} {P : Rep G n} {o : V→Site n} {T : Taste X o P R}

omit [Fintype V] in
private theorem tariff {I : Type} {p q : BudgetPoint} (fit : HasBudget p q)
    {w : V→ℝ} (hw : ∀ v,0<w v) (v : V) (z : I→R.Mode) (s : I→Support n)
    (k : I→ℝ) (hk : ∀ i,0≤k i) {b : ℝ}
    (paid : SumBudget (fun i => if v∈(z i).val then Poly.toll w (z i)*p.mass (s i) (k i) else 0) b) :
    SumBudget (fun i => if v∈(z i).val then Poly.toll w (z i)*q.mass (s i) (k i) else 0) b := by
  apply budget_mono paid
  · intro i
    split
    next => exact mul_nonneg (Poly.worth hw _).le ((hk i).trans (q.loMass _ _ (hk i)))
    next => exact le_rfl
  · intro i
    split
    next => exact mul_le_mul_of_nonneg_left (fit.mass _ (hk i)) (Poly.worth hw _).le
    next => exact le_rfl

omit [Fintype V] in
def restrict {p q : BudgetPoint} (fit : HasBudget p q) {w : V→ℝ} {b u v : ℝ}
    (h : FullBudget p T w b u v) : FullBudget q T w b u v := by
  refine {h with regular:=?_,regular_law:=?_,regularTotal:=?_,forcedTotal:=?_}
  · intro i
    refine ⟨?_⟩
    intro x v hv
    obtain ⟨f,positive,bill,read⟩ := (h.regular i).controls x v hv
    refine ⟨f,positive,?_,?_⟩
    · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ fit.order))
        (fun j _ _=>div_nonneg (positive j) (Nat.cast_nonneg _))).trans bill
    · intro dirs inside held U hU
      exact read dirs (inside.trans fit.order) (fun d hd=>fit.toHasJets.dirs _ (held d hd)) U
        (fit.threshold.symm ▸ hU)
  · intro x i
    have a := h.regular_law x i
    exact {a with
      smooth:=fun U hu=>(a.smooth U (fit.threshold.symm ▸ hu)).of_le (by exact_mod_cast fit.order)
      hasDerivs:=fun U hu d k hk=>a.hasDerivs U (fit.threshold.symm ▸ hu) d k (hk.trans_le fit.order)}
  · intro t
    obtain ⟨e,k,he,hk,hc⟩:=h.regularTotal t
    exact ⟨e,k,tariff fit h.radii t _ _ _ h.white_nonnegative he,
      tariff fit h.radii t _ _ _ h.gold_nonnegative hk,hc⟩
  · intro t
    exact tariff fit h.radii t _ _ _ h.black_nonnegative (h.forcedTotal t)

theorem original (D : V→Orbit) (a : Bands (Stock.census V) P) {q : BudgetPoint}
    (fit : HasBudget P.p q) {w : V→ℝ} {c d b : ℝ} (hb : 0<b) (ha : a.Active)
    (hr : a.Radial w 0 c d b) :
    Nonempty (RelativeBudget q (WilsonRetainedPointBudget.table D a) w b
      (envelopeProduct (fun _ : V=>1)) (Real.exp 1*c) d) := by
  obtain ⟨h⟩ := WilsonRetainedPointBudget.divided D a hb ha hr
  have same (s : (Stock.census V).Mode) : envelopeProduct (fun _ : V=>1) s=1 := by
    simp [envelopeProduct]
  have eq : priceNormalized (envelopeProduct (fun _ : V=>1)) (WilsonRetainedPointBudget.table D a) =
      WilsonRetainedPointBudget.table D a := by
    simp [priceNormalized,same]
  exact ⟨⟨fun s=>by rw [same];exact zero_lt_one,same _,eq.symm ▸ restrict fit h⟩⟩

end YM.Integration.WilsonRetainedRequestedBudget

