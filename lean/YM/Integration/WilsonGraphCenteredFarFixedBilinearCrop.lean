import YM.Integration.WilsonGraphCenteredFarBilinearBook
import YM.Integration.WilsonGraphCenteredFarHighFieldCrop

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedFixedBilinearCrop

open Function Filter Real PowerSeries Finset Continuation Growth
open Register MS MS.Native MS.Land MS.Book MS.Book.Program
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Reg.Point
open AppointedScalarOverflow AppointedBilinearPrice
open scoped BigOperators Classical

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {simple : G.Simple} {P : MS.Land.Prescription (Press.portDeck G)}
  (H : Main.Match N simple M P true)

def secondField (h : ℕ) (s : ℝ) (farBorn : Bool) : Guard G h :=
  if farBorn then 1 else Kseries N M h s

/-- The kernel order p and the larger physical field order k are kept independent. -/
theorem read (h p k : ℕ) (x : Scale.Stage 2) (A B : Guard G h) (u v : Sec G h) (t : ℝ) :
    crop p t (Reg.Point.story (book N h 2 x) ![atColumn A k t u, atColumn B k t v]) =
      AppointedHighFieldCrop.bookValue N h p k x A B u v t := by
  have finite {I : Type} [Fintype I] (F : I → PowerSeries ℂ) : crop p t (∑ i,F i) = ∑ i,crop p t (F i) := by
    exact YM.FVA2.GradedFar.crop_sum p t Finset.univ F
  have fixed (a b : ℂ) (F : PowerSeries ℂ) : crop p t (C a*C b*F) = a*b*crop p t F := by
    rw [←map_mul, YM.FVA2.GradedFar.crop_C_mul]
  rw [AppointedBilinearBook.basis N,finite]
  unfold AppointedHighFieldCrop.bookValue
  refine sum_congr rfl fun c _ => ?_
  rw [fixed,AppointedBilinearBook.columnCoordinate,AppointedBilinearBook.columnCoordinate]

include H in
/-- Both birth patterns are priced on the same filed stage, with a constant fixed before
the log distance and the far heater. -/
theorem fixedProfile (h p k : ℕ) (hpk : p ≤ k) (x : Scale.Stage 2) (u v : Sec G h) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ a : ℕ, ∀ s ≥ 0, ∀ (t : ℝ), |t| ≤ 1 → ∀ (farBorn : Bool),
      let A := Kseries N M h s
      let B := secondField N M h s farBorn
      ‖crop p t (Reg.Point.story (book N h 2 x) ![atColumn A k t u,atColumn B k t v]) -
          crop p t (AppointedBilinearCauchy.full N h x A B u v)‖ ≤ D*|t|^(p+1)*(1+s)^a := by
  obtain ⟨E,hE,a,pay⟩ := AppointedBilinearPrice.fixedField N M H h k
  let I := Appointed220.Eval.mass k (Appointed220.Zones.liftSeries
    (AppointedCenteredSeriesPrice.coordinateChart G h) (1 : Guard G h))
  let J := max E I
  have hJ : 0 ≤ J := hE.trans (le_max_left _ _)
  let U (c : Fin 2 → Dime G h) := ‖readCoordinate h (c 0)‖*‖chair G h u‖
  let V (c : Fin 2 → Dime G h) := ‖readCoordinate h (c 1)‖*‖chair G h v‖
  let F (c : Fin 2 → Dime G h) := mass p (Reg.Point.story (book N h 2 x) (fun i => dime G h (c i)))
  have hU (c) : 0 ≤ U c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hV (c) : 0 ≤ V c := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hF (c) : 0 ≤ F c := sum_nonneg fun _ _ => norm_nonneg _
  let base := ∑ c, U c * V c * F c
  have hb : 0 ≤ base := sum_nonneg fun c _ => mul_nonneg (mul_nonneg (hU c) (hV c)) (hF c)
  refine ⟨4*base*J^2,mul_nonneg (mul_nonneg (by norm_num) hb) (sq_nonneg _),a+a,?_⟩
  intro s hs t ht farBorn
  let w := J*(1+s)^a
  have pow0 : 0 ≤ (1+s)^a := pow_nonneg (by linarith) _
  have w0 : 0 ≤ w := mul_nonneg hJ pow0
  have ew : E*(1+s)^a ≤ w := mul_le_mul_of_nonneg_right (le_max_left _ _) pow0
  have jw : J ≤ w := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow₀ (le_add_of_nonneg_right hs) (n:=a)) hJ
  have uBound (c) : mass k (tax (Kseries N M h s) u (c 0)) ≤ U c*w :=
    (pay s hs u (c 0)).trans (mul_le_mul_of_nonneg_left ew (hU c))
  have vBound (c) : mass k (tax (secondField N M h s farBorn) v (c 1)) ≤ V c*w := by
    cases farBorn with
    | false => exact (pay s hs v (c 1)).trans (mul_le_mul_of_nonneg_left ew (hV c))
    | true =>
      have fee := AppointedBilinearPrice.fieldMass k h (1:Guard G h) v (c 1)
      exact fee.trans (mul_le_mul_of_nonneg_left ((le_max_right E I).trans jw) (hV c))
  have bound := AppointedHighFieldCrop.expense N h p k hpk x (Kseries N M h s)
    (secondField N M h s farBorn) u v t ht
  dsimp only
  rw [read N]
  apply bound.trans
  have each (c) : mass k (tax (Kseries N M h s) u (c 0)) *
      mass k (tax (secondField N M h s farBorn) v (c 1)) * F c ≤ (U c*V c*F c)*w^2 := by
    have pp := mul_le_mul (uBound c) (vBound c) (sum_nonneg fun _ _ => norm_nonneg _) (mul_nonneg (hU c) w0)
    exact (mul_le_mul_of_nonneg_right pp (hF c)).trans_eq (by ring)
  have total := mul_le_mul_of_nonneg_left (sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin 2 → Dime G h))) => each c))
    (mul_nonneg (show (0:ℝ)≤4 by norm_num) (pow_nonneg (abs_nonneg t) (p+1)))
  refine total.trans_eq ?_
  rw [←Finset.sum_mul,pow_add]
  dsimp only [base,w];ring

end YM.FVA2.GradedFar.AppointedFixedBilinearCrop
