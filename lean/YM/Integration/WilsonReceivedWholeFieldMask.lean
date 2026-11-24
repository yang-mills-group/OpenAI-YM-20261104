import YM.Integration.WilsonRootedKioskCompleteFiling
import YM.Integration.PhysicalWilsonHotIntegral

/-! The complete filed group-field observable on a named exceptional collar
of the original Wilson course. Its external roots remain independent. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReceivedWholeFieldMask
open Function Finset Filter MeasureTheory Lattice Wilson RG Ac Marker QuadraticLocal
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums
open Push.AbsoluteSums.Animals OPE.Therm WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology

variable {G : Gauge} {n : Side} {p : BudgetPoint} {V I T : Type} [DecidableEq V]
  {Γ : Census V} {o : V → Site n} (L : Lamps T I G p o Γ)
  {w : V → ℝ} {a D : ℝ} (hw : ∀ v, 0 < w v) (ha : 0 ≤ a)
  (gross : Gross L w p.B a D)
include hw ha gross

theorem whole (t : T) (U : Config G n) (s : Γ.Mode) (v : V) (hv : v∈s.val) :
    Poly.toll w s * ‖(bare L t U).part s‖ ≤ D := by
  obtain ⟨f,pos,values,hit⟩ := gross.before
  let z (j : I) : ℂ := (Poly.toll w s:ℂ) * (Poly.send (L.mode j) (L.nominal t j U)).part s
  have wallet := hit (o v)
  have row (j : I) : ‖z j‖ ≤ if o v∈L.ground j then
      Poly.toll w (L.mode j)*f j*Real.exp (a*coverNumber p.B (L.ground j)) else 0 := by
    by_cases hm : s = L.mode j
    · have root : o v ∈ L.ground j := L.roots j v (hm ▸ hv)
      have fee := (Poly.worth hw s).le
      have width : 1≤Real.exp (a*coverNumber p.B (L.ground j)) :=
        Real.one_le_exp (mul_nonneg ha (Nat.cast_nonneg _))
      rw [if_pos root,←hm]
      simp only [z,Poly.part_send,if_pos hm,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg fee]
      exact (mul_le_mul_of_nonneg_left (values j t U) fee).trans
        (le_mul_of_one_le_right (mul_nonneg fee (pos _)) width)
    · simp only [z,Poly.part_send,if_neg hm,mul_zero,norm_zero]
      exact wallet.1 j
  have sums := wallet.2.1.of_nonneg_of_le (fun j => norm_nonneg (z j)) row
  have he : (Poly.toll w s:ℂ) * (bare L t U).part s = ∑'j,z j := by
    rw [WilsonRootedKioskOccupiedSlip.bare,Poly.share (WilsonRootedKioskCompleteFiling.sums L hw ha gross t U).1,tsum_mul_left]
  have estimate := (norm_tsum_le_tsum_norm sums).trans ((sums.tsum_le_tsum row wallet.2.1).trans wallet.2.2)
  rw [←he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Poly.worth hw s).le] at estimate
  exact estimate

theorem measurable [Countable I] (t : T) (s : Γ.Mode) :
    Measurable (fun U => (bare L t U).part s) := by
  have rows : ∀ U : Config G n, (bare L t U).part s =
      ∑'j, (Poly.send (L.mode j) (L.nominal t j U)).part s := fun U =>
    Poly.share (WilsonRootedKioskCompleteFiling.sums L hw ha gross t U).1 s
  simp_rw [rows]
  apply Measurable.tsum
  intro j
  by_cases hm : s = L.mode j
  · simpa only [Poly.part_send,if_pos hm] using (L.legal t j).borel
  · simp only [Poly.part_send,if_neg hm]
    exact measurable_const

end YM.Integration.WilsonReceivedWholeFieldMask
