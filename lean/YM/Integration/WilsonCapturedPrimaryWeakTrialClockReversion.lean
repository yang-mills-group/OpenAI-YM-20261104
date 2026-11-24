import YM.Integration.WilsonReceivedCanonicalSocketMist
import YM.Integration.WilsonConditionalTaylorWheelClock

/-! The physical scalar clock and its independent ordinary and connected single mark. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialClockReversion
open Finset PowerSeries FormalBulk08 FormalBulk08.Series FormalBulk08.Wine
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel.Mark
open scoped Classical BigOperators

theorem chart (V : Type) (A : Cost) :
    canter A A⁻¹ V = redo (U:=V) A := by
  apply serial_ext
  · rw [canter_X]
    exact (coeff_zero_eq_constantCoeff_apply _).symm.trans (grass A)
  · intro q
    induction q using MvPolynomial.induction_on with
    | C u =>
      rw [canter_C, insert_C]
      exact (redo_base A u).symm
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp =>
      have px : canter A A⁻¹ V (C (MvPolynomial.X j)) = redo A (C (MvPolynomial.X j)) := by
        rw [canter_C, insert_X, show C (MvPolynomial.X j) = path j from rfl, redo_path]
        rfl
      simp only [map_mul, hp, px]
  · rw [canter_X, redo_X]
    rfl

theorem dated {V : Type} (H : Cost) (unit : constantCoeff H = 1) (T : Ink V) :
    canter (bookH H) (bookU H) V T = redo (Blue.back H) T := by
  rw [←WilsonConditionalTaylorWheelClock.returned H unit,
    ←WilsonConditionalTaylorWheelClock.outgoing H unit, chart]

theorem solitary {I S : Type} [DecidableEq I] [CommRing S]
    {M L : Sac I S} (issued : Equation M L) (a : I) : M {a} = L {a} := by
  have square := congrFun issued.2.2 {a}
  have subsets : ({a}:Finset I).powerset = {∅, {a}} := by
    ext t
    simp [Finset.subset_singleton_iff]
  simpa [dial, shells, subsets, issued.1] using square

end YM.Integration.WilsonCapturedPrimaryWeakTrialClockReversion
