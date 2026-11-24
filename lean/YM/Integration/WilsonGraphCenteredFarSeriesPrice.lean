import YM.Integration.WilsonGraphCenteredFarReverseBudget
import YM.Integration.WilsonGraphOriginalReverseTariff

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedCenteredSeriesPrice

open Filter Real PowerSeries Growth Continuation
open Register MS MS.Book MS.Land Scale
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Enh O.Score O.Canon Scale Dframe Jury
open MS.Native MS.Book MS.Menus MS.Tide MS.Book.Program
open scoped Topology Classical BigOperators

/-- Use the public coordinate norm on both factors of the original noncommutative invoice. -/
def coordinateChart (G : Gauge) (h : ℕ) : (Module.End ℂ (Sec G h)) →ₐ[ℂ] Maps G h :=
  AlgHom.ofLinearMap (chairs G h).toLinearMap chairs_one (fun x y => chairs_mul x y)

theorem evaluated (G : Gauge) (h k : ℕ) (A : Guard G h) (t : ℝ) :
    Appointed220.Eval.value k (Appointed220.Zones.liftSeries (coordinateChart G h) A) (t:ℂ) =
      chairs G h (atColumn A k t) := by
  simp only [Appointed220.Eval.value, Appointed220.Eval.sumTo, Appointed220.Zones.liftSeries, atColumn, map_sum, map_smul, coeff_map]
  all_goals rfl

variable {G : Gauge} (N : Register.WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple}
  {P : MS.Land.Prescription (Press.portDeck G)} (matchData : Main.Match N simple M P true)

private abbrev bank := GroupS.gaugeN N.scheme N.criterion M (Teller.logNu 1)

include matchData

/-- Chronological substitution gives the same operator series as `Appointed220.Zones.backStory`. -/
theorem sameReverse (h : ℕ) (s : ℝ) :
    Appointed220.Zones.liftSeries (coordinateChart G h) (AppointedCenteredReverse.reverseSeries N M h s) =
      Appointed220.Zones.backStory (coordinateChart G h) (bank N M) (-s) := by
  let f := coordinateChart G h
  let A := Appointed220.Zones.carry f (bank N M) (-s)
  let B := Appointed220.Zones.backStory f (bank N M) (-s)
  let Y := Appointed220.Zones.liftSeries f (AppointedCenteredReverse.reverseSeries N M h s)
  have aY : A * Y = 1 := by
    change PowerSeries.map f.toRingHom (Kseries N M h (-s)) *
      PowerSeries.map f.toRingHom (AppointedCenteredReverse.reverseSeries N M h s) = 1
    rw [← map_mul, AppointedCenteredReverse.reverseIdentity N M matchData h s, map_one]
  have bA : B * A = 1 := Appointed220.Zones.fore (matchData.dilation (Teller.logNu 1)).check f (-s)
  change Y = B
  calc Y = 1 * Y := (one_mul Y).symm
       _ = (B * A) * Y := congrArg (fun u => u * Y) bA.symm
       _ = B := by rw [mul_assoc, aY, mul_one]

/-- `Appointed220.Zones.Telescope.reverse_price` bounds the product error for the two cropped
series at the stated distance exponent and output grade. -/
theorem defect (h k K L : ℕ) (net : L + 2 + K*h ≤ k) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x in 𝓝[>] (0:ℝ), ∀ s, G1.Wire.Edge K x (exp s) →
      ∀ t : ℝ, |t| ≤ 2*x →
      ‖chairs G h (atColumn (Kseries N M h (-s)) k t) *
        chairs G h (atColumn (AppointedCenteredReverse.reverseSeries N M h s) k t) - 1‖ ≤ D*x^L := by
  obtain ⟨D, hD, cash⟩ := Appointed220.Zones.Telescope.reverse_price
    (law := (matchData.dilation (Teller.logNu 1)).check) (f := coordinateChart G h)
    (q := k) (K := K) (L := L) net
  refine ⟨D, hD, ?_⟩
  filter_upwards [cash] with x hx
  intro s edge t heat
  have bound := hx (exp s) edge (t:ℂ) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using heat)
  rw [Appointed220.Zones.Budget.eta, Real.log_exp] at bound
  rw [← sameReverse N M matchData h s] at bound
  change ‖Appointed220.Eval.value k (Appointed220.Zones.liftSeries (coordinateChart G h) (Kseries N M h (-s))) (t:ℂ) *
    Appointed220.Eval.value k (Appointed220.Zones.liftSeries (coordinateChart G h)
      (AppointedCenteredReverse.reverseSeries N M h s)) (t:ℂ) - 1‖ ≤ D*x^L at bound
  simpa only [evaluated] using bound

end YM.FVA2.GradedFar.AppointedCenteredSeriesPrice

