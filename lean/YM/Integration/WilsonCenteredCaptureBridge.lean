import YM.Integration.WilsonCenteredCompulsoryOwners
import YM.Corona.Halo

/-! Resolve the regular spectator and its named hard partner before summing
them. The actual capture patch connects their complete original supports. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCaptureBridge
open Finset Lattice RG Wilson Marker QuadraticLocal Ac Corona Push.AbsoluteSums
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
    {R : Census V} {o : V → Site n} {P : Rep G n}

theorem original (D : Lamps X ι G P.p o R)
    (K : Hard X P.p P.activities.forced P.activities.K o R) (w : V → ℝ)
    (hw : ∀ v, 0 < w v) {α δ κ : ℝ} (width : 0 ≤ α)
    (regular : D.Paid w P.p.B α δ) (hard : K.Paid w P.p.B α κ) (a b : V)
    (Z : Support n) (za : o a ∈ Z) (zb : o b ∈ Z) (x : X) (U : Config G n) :
    SumBudget (fun z : ι × ℕ =>
      (w a * ‖(D.frame z.1 x U).part (R.fire a)‖) *
        (w b * ‖(K.hard x z.2 U).part (R.fire b)‖) *
        Real.exp (α * coverNumber P.p.B (D.ground z.1 ∪ Z ∪ (P.activities.forced z.2).support)))
      (Real.exp (α * coverNumber P.p.B Z) * (δ*κ)) := by
  classical
  obtain ⟨f, positive, caps, billed⟩ := regular.budget
  obtain ⟨g, covers, spent⟩ := hard.wages
  let d := fun i : ι => (D.frame i x U).part (R.fire a)
  let k := fun i : ℕ => (K.hard x i U).part (R.fire b)
  have ed (i : ι) : w a * ‖d i‖ ≤ Poly.toll w (D.mode i)*f i := by
    have bill := Poly.member hw (R.fire a) (D.frame i x U)
    have lim : Poly.price w (D.frame i x U) ≤ Poly.toll w (D.mode i)*f i := by
      rw [Lamps.frame, Poly.solo]
      exact mul_le_mul_of_nonneg_left (D.light_size i x U (caps i x _ (D.address i).anchor))
        (Poly.worth hw _).le
    simpa only [d,Poly.toll,Census.fire,prod_singleton] using bill.trans lim
  have ek (i : ℕ) : w b * ‖k i‖ ≤ Poly.price w (g i) := by
    have bill := (Poly.member hw (R.fire b) (K.hard x i U)).trans ((covers i x U).reprice w hw)
    simpa only [k,Poly.toll,Census.fire,prod_singleton] using bill
  let m := Real.exp (α * coverNumber P.p.B Z)
  have overall := budget_scale (Real.exp_pos (α * coverNumber P.p.B Z)).le
    (budget_prod (billed (o a)) (spent (o b)))
  refine budget_mono overall (fun z => by positivity [hw a,hw b]) ?_
  rintro ⟨i,j⟩
  by_cases hd : d i = 0
  · change w a*‖d i‖*(w b*‖k j‖)*_ ≤ _
    rw [hd,norm_zero,mul_zero,zero_mul,zero_mul]
    exact overall.1 (i,j)
  by_cases hk : k j = 0
  · change w a*‖d i‖*(w b*‖k j‖)*_ ≤ _
    rw [hk,norm_zero,mul_zero,mul_zero,zero_mul]
    exact overall.1 (i,j)
  have inside : o a ∈ D.ground i := by
    have mode : R.fire a = D.mode i := by
      by_contra! wrong
      exact hd (by simp [d,Lamps.frame,Poly.part_send,wrong])
    apply D.roots i
    rw [← mode]
    exact mem_singleton_self _
  have within : o b ∈ (P.activities.forced j).support :=
    (K.locality x j).carry U (R.fire b) hk b (mem_singleton_self _)
  have geo : coverNumber P.p.B (D.ground i ∪ Z ∪ (P.activities.forced j).support) ≤
      coverNumber P.p.B Z + coverNumber P.p.B (D.ground i) + coverNumber P.p.B (P.activities.forced j).support := by
    have hz := meets_sum inside za P.p.B
    have hp := meets_sum (mem_union_right (D.ground i) zb) within P.p.B
    omega
  have geoR : (coverNumber P.p.B (D.ground i ∪ Z ∪ (P.activities.forced j).support) : ℝ) ≤
      (coverNumber P.p.B Z : ℝ) + coverNumber P.p.B (D.ground i) + coverNumber P.p.B (P.activities.forced j).support := by
    exact_mod_cast geo
  have strip := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left geoR width)
  simp only [mul_add,Real.exp_add] at strip
  simp only [if_pos inside,if_pos within]
  change w a*‖d i‖*(w b*‖k j‖)*_ ≤ _
  calc
    _ ≤ (Poly.toll w (D.mode i)*f i * Poly.price w (g j)) *
        (Real.exp (α*coverNumber P.p.B Z) * Real.exp (α*coverNumber P.p.B (D.ground i)) *
         Real.exp (α*coverNumber P.p.B (P.activities.forced j).support)) := by
      apply mul_le_mul _ strip (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (Poly.worth hw _).le (positive i)) (Poly.nonnegative hw _))
      exact mul_le_mul (ed i) (ek j) (mul_nonneg (hw b).le (norm_nonneg _))
        (mul_nonneg (Poly.worth hw _).le (positive i))
    _ = _ := by ring

end YM.Integration.WilsonCenteredCaptureBridge
