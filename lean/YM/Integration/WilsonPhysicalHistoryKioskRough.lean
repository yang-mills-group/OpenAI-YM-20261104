import YM.QuadraticLocal.Canopy
import YM.Push.GRID_APPROXIMATION.Hit

/-! The signed rough re-expression on a specified occupied mode. Each
contributing row carries every name in that mode. One of those names pays
the whole sum in the original rooted budget. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskRough
open Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums QuadraticLocal
open scoped Classical BigOperators

variable {V T E : Type} [DecidableEq V] {G : Gauge} {n : Side} {p : BudgetPoint}
  {R : Census V} {o : V → Site n} (M : Canopy.ShiftRows T E G p o R)
  {w : V → ℝ} (pos : ∀ v, 0 < w v) {B : ℕ} {a cost : ℝ} (expo : 0 ≤ a)
  (paid : M.Budget w B a cost)

include pos expo paid in
theorem occupied (s : R.Mode) (v : V) (live : v ∈ s.val) (t : T) (U : Config G n) :
    Poly.toll w s * ‖(M.log t U).part s‖ ≤
      Real.exp (-a*(coverNumber B (s.val.image o) : ℝ))*cost := by
  let D := coverNumber B (s.val.image o)
  obtain ⟨f,covers,bill⟩ := paid.earned
  have major := budget_scale (Real.exp_pos (-a*(D:ℝ))).le (bill (o v))
  have rows : SumBudget (fun i => Poly.toll w s * ‖(M.soap t i U).part s‖)
      (Real.exp (-a*(D:ℝ))*cost) := by
    apply budget_mono major (fun _ => mul_nonneg (Poly.worth pos s).le (norm_nonneg _))
    intro i
    by_cases h : (M.soap t i U).part s=0
    · rw [h,norm_zero,mul_zero]
      exact major.1 i
    have placed := (M.cost t i).carry U s h
    have extent : D ≤ coverNumber B (M.place i).val := by
      apply Corona.cover_mono _ B
      exact image_subset_iff.mpr placed
    have scale : 1 ≤ Real.exp (-a*(D:ℝ))*Real.exp (a*coverNumber B (M.place i).val) := by
      rw [← Real.exp_add,Real.one_le_exp_iff]
      have hd := mul_le_mul_of_nonneg_left (show (D:ℝ) ≤ coverNumber B (M.place i).val by exact_mod_cast extent) expo
      linarith
    have price : Poly.toll w s*‖(M.soap t i U).part s‖ ≤ Poly.price w (f i) := by
      calc
        _ ≤ Poly.toll w s*‖(f i).part s‖ := mul_le_mul_of_nonneg_left
          ((covers i t U s).1.trans (Complex.re_le_norm _)) (Poly.worth pos s).le
        _ ≤ _ := single_le_sum (fun u _ => mul_nonneg (Poly.worth pos u).le (norm_nonneg _)) (mem_univ s)
    change _ ≤ Real.exp (-a*(D:ℝ))*(if o v∈(M.place i).val then _ else 0)
    rw [if_pos (placed v live)]
    exact price.trans ((le_mul_of_one_le_right (Poly.nonnegative pos _) scale).trans_eq (by ring))
  have ht := Poly.worth pos s
  have norms : Summable (fun i => ‖(M.soap t i U).part s‖) :=
    (summable_mul_left_iff ht.ne').mp rows.2.1
  rw [Canopy.ShiftRows.log,Poly.share (M.earnings paid pos expo t U) s]
  apply (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm norms) ht.le).trans
  rw [← tsum_mul_left]
  exact rows.2.2

include pos expo paid in
theorem separated (s : R.Mode) (v u : V) (hv : v ∈ s.val) (hu : u ∈ s.val) (t : T) (U : Config G n) :
    Poly.toll w s * ‖(M.log t U).part s‖ ≤
      Real.exp (-a*(separation (o v) (o u)/Push.GridApprox.Attach.leg B : ℕ))*cost := by
  have span := Push.GridApprox.Attach.distance_charge (s.val.image o) B (o v) (o u)
    (mem_image_of_mem _ hv) (mem_image_of_mem _ hu)
  have receipt := paid.earned.choose_spec.2 (o v)
  have hc : 0 ≤ cost := (tsum_nonneg receipt.1).trans receipt.2.2
  apply (occupied M pos expo paid s v hv t U).trans
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
    (show ((separation (o v) (o u)/Push.GridApprox.Attach.leg B : ℕ):ℝ) ≤ coverNumber B (s.val.image o) by exact_mod_cast span) (neg_nonpos.mpr expo))) hc

end YM.Integration.WilsonPhysicalHistoryKioskRough

