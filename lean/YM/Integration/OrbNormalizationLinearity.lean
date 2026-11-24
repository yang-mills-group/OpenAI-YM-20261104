import YM.PertExtension.Normalized

/-! Scalar extraction from the original normalized inversion prescription.
The numerator and every coefficient use the same unchanged vacuum. The
coefficient identity follows from the native finite-regulator asymptotics;
no compatibility equation or infrared estimate is assumed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OrbNormalizationLinearity
open Function Lattice MeasureTheory
open PertExtension PertExtension.Orb PertExtension.Series.Tested
open scoped BigOperators Classical Topology
variable {G : Gauge} {n : Side}

theorem numerator_const_mul (O : Orb.Observable G n) (c t : ℝ) :
    Orb.numerator (fun x => c * O x) t = c * Orb.numerator O t := by
  unfold Orb.numerator Orb.entries
  simp_rw [mul_assoc]
  exact integral_const_mul c _

theorem expectation_const_mul (O : Orb.Observable G n) (c : ℝ) :
    Orb.expectation (fun x => c * O x) = fun t => c * Orb.expectation O t := by
  funext t
  change Orb.numerator (fun x => c * O x) t / Orb.numerator 1 t =
    c * (Orb.numerator O t / Orb.numerator 1 t)
  rw [numerator_const_mul]
  ring

theorem localTest_const_mul {O : Orb.Observable G n} (h : Orb.LocalTest O)
    (c : ℝ) : Orb.LocalTest (fun x => c * O x) :=
  ⟨continuous_const.mul h.boundedness, contDiffAt_const.mul h.germ⟩

theorem diagonal_const_mul {O : Orb.Observable G n} (he : Even n.val)
    (h : Orb.LocalTest O) (c : ℝ) :
    Orb.diag (fun x => c * O x) = fun k => c * Orb.diag O k := by
  have hc : Aspiration (fun _ : ℝ => c) (fun i => if i = 0 then c else 0) := by
    simpa using (Aspiration.single c 0)
  have hs := hc.prod (Orb.finite_formula he (Orb.traySpec G) h)
  have hp : PowerSeries.mk (fun i => if i = 0 then c else 0) = PowerSeries.C c := by
    ext i : 1
    simp [PowerSeries.coeff_C]
  have hv : conv (fun i => if i = 0 then c else 0) (Orb.diag O) =
      fun k => c * Orb.diag O k := by
    funext k
    rw [conv, term, hp, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  change Aspiration ((fun _ : ℝ => c) * Orb.expectation O)
    (conv (fun i => if i = 0 then c else 0) (Orb.diag O)) at hs
  rw [hv] at hs
  have hf : (fun _ : ℝ => c) * Orb.expectation O =
      Orb.expectation (fun x => c * O x) := (expectation_const_mul O c).symm
  rw [hf] at hs
  exact (Orb.finite_formula he (Orb.traySpec G) (localTest_const_mul h c)).unique hs

theorem restricted_diagonal_const_mul {O : Wilson.Config G n → ℝ}
    (he : Even n.val) (h : Orb.PreTest O) (c : ℝ) (k : ℕ) :
    Orb.diag (Orb.restrictedO (fun U => c * O U)) k =
      c * Orb.diag (Orb.restrictedO O) k :=
  congrFun (diagonal_const_mul he h.curved c) k

end YM.Integration.OrbNormalizationLinearity
