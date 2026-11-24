import YM.Integration.WilsonGraphCenteredFarSignedInsertion
import YM.Integration.WilsonGraphCenteredFarFixedBilinearCrop

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedUniformBilinearStock
open Function Finset PowerSeries Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open AppointedScalarOverflow AppointedBilinearPrice
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
  (H : Main.Match N simple M P true)

theorem massSum {I : Type} [Fintype I] (p : ℕ) (v : I → PowerSeries ℂ) :
    mass p (∑ i,v i) ≤ ∑ i,mass p (v i) := by
  unfold mass
  simp only [map_sum]
  exact (sum_le_sum fun j _ => norm_sum_le _ (fun i => coeff j (v i))).trans_eq sum_comm

theorem fullMass (h p : ℕ) (x : Scale.Stage 2) (A B : Guard G h) (u v : Sec G h) :
    mass p (AppointedBilinearCauchy.full N h x A B u v) ≤
      ∑ c : Fin 2 → Dime G h, mass p (tax A u (c 0))*mass p (tax B v (c 1))*
        mass p (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i))) := by
  unfold AppointedBilinearCauchy.full
  refine (massSum p _).trans (sum_le_sum fun c _ => ?_)
  let F := Reg.Point.story (book N h 2 x) (fun i => dime G h (c i))
  exact (massProduct p _ F).trans (mul_le_mul_of_nonneg_right (massProduct p _ _)
    (sum_nonneg fun _ _ => norm_nonneg _))

include H in
/-- Only the scalar kernel budget varies with the stage. All clock and field
constants are chosen before the separated point and both occupied marks. -/
theorem uniform (h p k : ℕ) : ∃ E : ℝ, 0 ≤ E ∧ ∃ a : ℕ, ∀ s ≥ 0, ∀ farBorn : Bool,
    ∀ (x : Scale.Stage 2) (u v : Sec G h),
    let A := Kseries N M h s
    let B := AppointedFixedBilinearCrop.secondField N M h s farBorn
    (∑ c : Fin 2 → Dime G h, mass k (tax A u (c 0))*mass k (tax B v (c 1))*
      mass p (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i)))) ≤
      AppointedSignedInsertion.budget N h p x*‖chair G h u‖*‖chair G h v‖*(E*(1+s)^a) := by
  obtain ⟨E,hE,a,paid⟩ := AppointedBilinearPrice.fixedField N M H h k
  let I := Appointed220.Eval.mass k (Appointed220.Zones.liftSeries
    (AppointedCenteredSeriesPrice.coordinateChart G h) (1:Guard G h))
  let J := max E I
  have hJ : 0 ≤ J := hE.trans (le_max_left _ _)
  refine ⟨J^2,sq_nonneg _,a+a,?_⟩
  intro s hs farBorn x u v A B
  let w := J*(1+s)^a
  have hp : 0 ≤ (1+s)^a := pow_nonneg (by linarith) _
  have hw : 0 ≤ w := mul_nonneg hJ hp
  have ew : E*(1+s)^a ≤ w := mul_le_mul_of_nonneg_right (le_max_left _ _) hp
  have jw : J ≤ w := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_pow₀ (le_add_of_nonneg_right hs) (n:=a)) hJ
  let F (c : Fin 2 → Dime G h) := mass p
    (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i)))
  have f0 (c) : 0 ≤ F c := sum_nonneg fun _ _ => norm_nonneg _
  have one (c : Fin 2 → Dime G h) :
      mass k (tax A u (c 0)) ≤ (‖readCoordinate h (c 0)‖*‖chair G h u‖)*w :=
    (paid s hs u _).trans (mul_le_mul_of_nonneg_left ew (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have two (c : Fin 2 → Dime G h) :
      mass k (tax B v (c 1)) ≤ (‖readCoordinate h (c 1)‖*‖chair G h v‖)*w := by
    cases farBorn with
    | false => exact (paid s hs v _).trans (mul_le_mul_of_nonneg_left ew (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    | true =>
      have fee := AppointedBilinearPrice.fieldMass k h (1:Guard G h) v (c 1)
      exact fee.trans
        (mul_le_mul_of_nonneg_left ((le_max_right E I).trans jw) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have each (c : Fin 2 → Dime G h) : mass k (tax A u (c 0))*mass k (tax B v (c 1))*F c ≤
      ((‖readCoordinate h (c 0)‖*‖readCoordinate h (c 1)‖)*F c)*
        ‖chair G h u‖*‖chair G h v‖*(J^2*(1+s)^(a+a)) := by
    have e := mul_le_mul (one c) (two c) (sum_nonneg fun _ _ => norm_nonneg _)
      (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hw)
    exact (mul_le_mul_of_nonneg_right e (f0 c)).trans_eq (by dsimp only [w]; rw [pow_add];ring)
  exact (sum_le_sum fun c _ => each c).trans_eq (by unfold AppointedSignedInsertion.budget; simp only [sum_mul];rfl)

end YM.FVA2.GradedFar.AppointedUniformBilinearStock
