import YM.Integration.WilsonPositionThermometerFinite
import YM.Integration.WilsonPositionIndependentIntegral

/-! One original signed three-position integral for the discrepancy of the
measured position coupling from the independently computed MS program.
The scalar contains both proper partitions and the actual first coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerDefect
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose FVA2 FVA2.Arrival FVA2.Register FVA2.Scale MS MS.Land
open WilsonIndependentSchemeTruncation
open scoped Topology BigOperators Classical Polynomial
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S) (Z : WilsonPrescription G) (ν : ℝ)
variable (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (q : ℕ) (r t : ℝ)

def residue (z : UVIndex) : ℝ :=
  ((Rose.test Z.criterion).applyTo (fun x =>
    WilsonPositionThermometerRegulator.full J r z x -
      WilsonPositionIndependentIntegral.positive Z ν T q t x)).re / Rose.c_T Z.criterion

def continuum : ℝ :=
  ((Rose.test Z.criterion).applyTo (fun x =>
    WilsonPositionThermometerPhases.raw F J none r x -
      WilsonPositionIndependentIntegral.positive Z ν T q t x)).re / Rose.c_T Z.criterion

private theorem integrable_fine (z : UVIndex) :
    Integrable (fun x : Points 3 => Rose.test Z.criterion x*WilsonPositionThermometerRegulator.full J r z x) := by
  let Φ := Rose.test Z.criterion
  let X := R.family.side z.1 z.2
  let a (x : Fin 3 → Site X) := WilsonPositionThermometerConnected.value (fun s =>
    R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3=>6) x (WilsonPositionThermometerRegulator.written J r s))
  let m := ∑ x : Fin 3 → Site X,‖a x‖
  have ga : Integrable (fun x : Points 3 => Φ x) := Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport
  apply (ga.norm.mul_const m).mono' (Φ.continuous.measurable.mul (WilsonPositionThermometerFinite.measurable J r z)).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  let v : Fin 3 → Site X := wrap X ∘ Extraction.address (R.family.S.a z.1) (r • x)
  change ‖Φ x*WilsonPositionThermometerRegulator.full J r z x‖ ≤ ‖Φ x‖*m
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.single_le_sum (f:=fun y => ‖a y‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ v)

private theorem subtracted (φ : Test 3) {A B : Points 3 → ℂ}
    (ha : Integrable (fun x => φ x*A x)) (hb : Integrable (fun x => φ x*B x)) :
    φ.applyTo (fun x => A x-B x) = φ.applyTo A-φ.applyTo B := by
  unfold Test.applyTo
  simp only [mul_sub]
  exact integral_sub ha hb

theorem actual (z : UVIndex) :
    residue J Z ν T q r t z = WilsonPositionThermometerFinite.finite J r Z.criterion z -
      ((finite q (Measure.chi Z.criterion ν T)).eval (t:ℂ)).re := by
  rw [WilsonPositionIndependentIntegral.real_polynomial]
  unfold residue WilsonPositionThermometerFinite.finite
  rw [subtracted _ (integrable_fine J Z r z) ((Rose.test Z.criterion).smearing
    (WilsonPositionIndependentIntegral.positive_continuous Z ν T q t)),Complex.sub_re,sub_div]

theorem reference (hr : 0<r) :
    continuum F J Z ν T q r t = WilsonPositionThermometerReading.reading F J Z.criterion r -
      ((finite q (Measure.chi Z.criterion ν T)).eval (t:ℂ)).re := by
  rw [WilsonPositionIndependentIntegral.real_polynomial]
  unfold continuum WilsonPositionThermometerReading.reading WilsonPositionThermometerReading.tested
  rw [subtracted _ ((Rose.test Z.criterion).smearing (WilsonPositionThermometerTest.continuous F J none hr))
    ((Rose.test Z.criterion).smearing (WilsonPositionIndependentIntegral.positive_continuous Z ν T q t)),
    Complex.sub_re,sub_div]
  rfl

theorem original (hG : G.Simple) {l : Filter UVIndex} (hl : l ≤ f.fuse) (hr : 0<r) :
    Tendsto (residue J Z ν T q r t) l (𝓝 (continuum F J Z ν T q r t)) := by
  rw [reference F J Z ν T q r t hr]
  apply ((WilsonPositionThermometerFinite.original F J r Z.criterion hG hl hr).sub_const ((finite q (Measure.chi Z.criterion ν T)).eval (t:ℂ)).re).congr'
  exact Eventually.of_forall (fun z => (actual J Z ν T q r t z).symm)

variable {T}
theorem first {hG : G.Simple} {Q : Prescription (Press.portDeck G)} {dial : Bool}
    (M : Main.Match Z hG T Q dial) (hr : 0<r) :
    continuum F J Z ν T 1 r t = WilsonPositionThermometerReading.reading F J Z.criterion r - t := by
  rw [reference F J Z ν T 1 r t hr,WilsonPositionIndependentIntegral.linear Z ν M t,Complex.ofReal_re]

end YM.Integration.WilsonPositionThermometerDefect
