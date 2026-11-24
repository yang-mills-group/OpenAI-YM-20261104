import YM.Integration.WilsonReceivedOrdinaryHearing

/-! A finite filed counterterm on its common physical and independent moment tables. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCloseCounterterm
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Cumulants
open WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

theorem one (W : Grade R r) (unit : UnitLeading W) (sym : Symmetric W) (g : ℂ) (a : V) :
    (value g (logMarked W)).part (R.fire a)=(value g (ratio W)).part (R.fire a) := by
  let P := render (ratio W)
  let B := logSeries (Fintype.card V+r) P
  have restore : stamp R r P=ratio W := rerender (sym_ratio unit sym)
  have filed : stamp R r B=logMarked W := by
    change stamp R r (logSeries (Fintype.card V+r) P) = logMarked W
    rw [stamp_log,restore,logMarked,log_to (ratio W) (ratio_quiet unit) (Fintype.card V+r)
      (room_for (Fintype.card V) (fun t=>Finset.card_le_univ t.val))]
  rw [←filed,←restore,stamped,stamped]
  exact congrArg (partialValue r g) (single W unit a)

theorem singleton (Y : Poly R) (quiet : Y.part R.quiet=1) (W : Grade R r)
    (unit : UnitLeading W) (sym : Symmetric W) (g : ℂ) (a : V) :
    (logTo (Fintype.card V) Y-value g (logMarked W)).part (R.fire a) =
      Y.part (R.fire a)-(value g (ratio W)).part (R.fire a) := by
  rw [←log_to Y quiet _ (fun t=>Finset.card_le_univ t.val),part_sub,lamp a Y quiet,one W unit sym g a]

def compensated (Y : Poly R) (s : R.Mode) (names : Finset V) (c : V → ℂ) :=
  Y.part s - ∑ v ∈ names,c v*Y.part (R.fire v)

omit [Fintype V] in
/-- Keep the pair once and weight each separately enrolled singleton by its own
filed coefficient, on the same two complete moment tables. -/
theorem linear (Y Z : Poly R) (a : V) (s : R.Mode) (names : Finset V) (c : V → ℂ)
    (pairPrice : ℝ) (fee : V → ℝ)
    (pair : ‖(Y.part s-Y.part (R.fire a))-(Z.part s-Z.part (R.fire a))‖ ≤ pairPrice)
    (onePrice : ‖Y.part (R.fire a)-Z.part (R.fire a)‖ ≤ fee a)
    (rows : ∀ v ∈ names, ‖Y.part (R.fire v)-Z.part (R.fire v)‖ ≤ fee v) :
    ‖compensated Y s names c-compensated Z s names c‖ ≤
      pairPrice+fee a+∑ v ∈ names, ‖c v‖ * fee v := by
  let D := (Y.part s-Y.part (R.fire a))-(Z.part s-Z.part (R.fire a))
  let h := Y.part (R.fire a)-Z.part (R.fire a)
  let rest := ∑ v ∈ names, c v*(Y.part (R.fire v)-Z.part (R.fire v))
  have regroup : compensated Y s names c-compensated Z s names c=(D+h)-rest := by
    simp only [compensated,D,h,rest,mul_sub,sum_sub_distrib]
    ring
  have billed : ‖rest‖ ≤ ∑ v ∈ names, ‖c v‖*fee v := by
    apply (norm_sum_le ..).trans
    refine sum_le_sum fun v hv => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (rows v hv) (norm_nonneg _)
  rw [regroup]
  exact (norm_sub_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add pair onePrice)) billed)

end YM.Integration.WilsonReceivedCloseCounterterm
