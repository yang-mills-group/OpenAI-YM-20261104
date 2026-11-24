import YM.Integration.WilsonReceivedCenteredChart

/-! The ordinary singleton coefficients used in the signed capture can all be
read from the graded connected output of the same finite prescription. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedSingletonMass
open Finset Marker Extra.Trajectories Comparison.RG02 Comparison.RG02.Order
open WilsonIndependentOrdinaryPairGrade
open scoped Classical BigOperators

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

theorem coefficient (W : Grade R r) (unit : UnitLeading W) (sym : Symmetric W)
    (a : V) {j : ℕ} (hj : j ≤ r) :
    (slot (R.fire a) (render (ratio W))).coeff j =
      (observe R r (logMarked W) j).part (R.fire a) := by
  let P := render (ratio W)
  let B := logSeries (Fintype.card V+r) P
  have castLog : stamp R r B = logMarked W := by
    change stamp R r (logSeries (Fintype.card V+r) P) = _
    rw [stamp_log, show stamp R r P = ratio W from rerender (sym_ratio unit sym),
      logMarked, log_to (ratio W) (ratio_quiet unit) (Fintype.card V+r)
        (room_for (Fintype.card V) (fun t => Finset.card_le_univ t.val))]
  calc
    _ = (slot (R.fire a) B).coeff j :=
      congrArg (fun p : Polynomial ℂ => p.coeff j) (single W unit a).symm
    _ = (B.coeff j).part (R.fire a) := coeff_slot _ _ _
    _ = _ := by rw [←castLog,←series_poly R r B,observation R r _ hj,Polynomial.coeff_coe]

theorem bill (W : Grade R r) (unit : UnitLeading W) (sym : Symmetric W) (a : V) :
    mass (slot (R.fire a) (render (ratio W))) =
      ∑ j∈range (r+1), ‖(observe R r (logMarked W) j).part (R.fire a)‖ := by
  let p := slot (R.fire a) (render (ratio W))
  have sub : p.support ⊆ range (r+1) := by
    intro j hj
    by_contra h
    have large : ¬ j ≤ r := by simpa only [mem_range,Nat.lt_succ_iff] using h
    have zero : p.coeff j = 0 := by
      rw [show p.coeff j = _ from coeff_slot (R.fire a) _ j,
        render_coeff,observe,if_neg large,Poly.part_nil]
    exact (Polynomial.mem_support_iff.mp hj) zero
  change ∑ j∈p.support, ‖p.coeff j‖ = _
  calc
    _ = ∑ j∈range (r+1), ‖p.coeff j‖ := sum_subset sub (fun j _ hj => by
          rw [Polynomial.notMem_support_iff.mp hj,norm_zero])
    _ = _ := sum_congr rfl (fun j hj => congrArg norm
      (coefficient W unit sym a (Nat.le_of_lt_succ (mem_range.mp hj))))

theorem measured (W : Grade R r) (unit : UnitLeading W) (sym : Symmetric W)
    (a : V) (z : ℂ) (small : ‖z‖ ≤ 1) :
    ‖(value z (logMarked W)).part (R.fire a)‖ ≤ mass (slot (R.fire a) (render (ratio W))) := by
  rw [bill W unit sym a,vpart]
  refine (norm_sum_le ..).trans (sum_le_sum (fun j _ => ?_))
  rw [norm_mul,norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) small)

theorem issued (W : Grade R r) (unit : UnitLeading W) (sym : Symmetric W)
    (a : V) (κ : ℝ) (fare seam : ℕ → ℝ) (file : ℕ → Poly R)
    (positive : 0 ≤ κ)
    (reported : ∀ j ≤ r, ∃ e : Poly R, observe R r (logMarked W) j = file j + e ∧
      κ * ‖e.part (R.fire a)‖ ≤ seam j)
    (paid : ∀ j ≤ r, κ * ‖(file j).part (R.fire a)‖ ≤ fare j) :
    κ * mass (slot (R.fire a) (render (ratio W))) ≤
      ∑ j∈range (r+1), (fare j + seam j) := by
  rw [bill W unit sym a,mul_sum]
  refine sum_le_sum (fun j hj => ?_)
  have bound := Nat.le_of_lt_succ (mem_range.mp hj)
  obtain ⟨e,eqn,miss⟩ := reported j bound
  rw [eqn]
  change κ * ‖(file j).part (R.fire a) + e.part (R.fire a)‖ ≤ _
  calc
    _ ≤ κ*(‖(file j).part (R.fire a)‖+‖e.part (R.fire a)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le ..) positive
    _ ≤ _ := by rw [mul_add]; exact add_le_add (paid j bound) miss

end YM.Integration.WilsonReceivedSingletonMass
