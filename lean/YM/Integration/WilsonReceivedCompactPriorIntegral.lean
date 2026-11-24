import YM.Integration.WilsonReceivedGeometricCoveredPrior
import YM.Integration.WilsonSeparatedOriginalThermometerCells

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCompactPriorIntegral
open Filter Finset MeasureTheory Lattice Wilson RG Source FVA1
open OPE OPE.Orbits OPE.Therm Climb Trace.Pilot PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open XSpace XSpace.Rose Push.GridApprox
open scoped BigOperators Topology Classical

variable {G:Gauge} (R:Run G) {N per i:ℕ} (live:i ≤ N)
variable {S:Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

include live in
/-- An exact finite sampling of the submitted physical profile before the complete original
transport. All placements have the same positive Wilson denominator at the reporting date. -/
theorem tested (test:Test 3) (χ:Points 3 → S) (measured:Measurable χ)
    (Z:S → Config G (R.family.side i per) → ℂ) (D₀:ℝ)
    (env:∀ y, RG.Envelope (Z y))
    (cost:∀ y,(∫ U,‖Z y U‖ ∂scene R.family.path N per i) ≤ D₀) :
    let result:=fun U=>test.applyTo (fun x=>Z (χ x) U)
    (∀ U,result U=∑ y,WilsonSeparatedOriginalThermometerCells.weight test χ y*Z y U) ∧
    RG.Envelope result ∧ ∀ j (age:j ≤ i),
      (∫ U,‖actualTransport R.family (N:=N) result age U‖ ∂scene R.family.path N per j) ≤
        (∫x:Points 3,‖test x‖)*D₀ := by
  intro result
  let w:=WilsonSeparatedOriginalThermometerCells.weight test χ
  let μ:=scene R.family.path N per i
  haveI : IsProbabilityMeasure μ:=OPE.Therm.probability (H:=R.family.path) (p:=per) R.makes.wilson live
  have d0:0≤D₀:=(integral_nonneg (fun U=>norm_nonneg (Z (χ 0) U))).trans (cost (χ 0))
  have same:result=fun U=>∑y:S,w y*Z y U := funext (fun U=>
    WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun y=>Z y U))
  refine ⟨fun U=>congrFun same U,?_⟩
  rw [same]
  choose b price using fun y=>(env y).cost
  have full:RG.Envelope (fun U=>∑y:S,w y*Z y U):=⟨Finset.measurable_fun_sum _ (fun y _=>measurable_const.mul (env y).meas),
    ∑y:S,‖w y‖*b y,fun U=>(norm_sum_le ..).trans <| Finset.sum_le_sum (fun y _=>by
      rw [norm_mul];exact mul_le_mul_of_nonneg_left (price y U) (norm_nonneg _))⟩
  refine ⟨full,?_⟩
  intro j age
  have each (y):Integrable (Z y) μ:=Integrable.of_bound (env y).meas.aestronglyMeasurable (b y)
    (ae_of_all _ (price y))
  have scalar (y):Integrable (fun U=>‖w y‖*‖Z y U‖) μ:=(each y).norm.const_mul _
  calc
    _ ≤ ∫ U,‖∑y:S,w y*Z y U‖ ∂μ:=ActualWilsonAbsoluteTransport.first R.family R.makes live
      (ActualWilsonAbsoluteTransport.weighted R.family R.makes live full) age
    _ ≤ ∫ U,∑y:S, ‖w y‖*‖Z y U‖ ∂μ:=by
      obtain ⟨B,hB⟩:=full.cost
      apply integral_mono (Integrable.of_bound full.meas.aestronglyMeasurable B (ae_of_all _ hB)).norm
        (integrable_finsetSum _ (fun y _=>scalar y))
      intro U
      simpa only [norm_mul] using (norm_sum_le univ (fun y=>w y*Z y U))
    _ = ∑y:S,‖w y‖*(∫U,‖Z y U‖ ∂μ):=by
      rw [integral_finsetSum _ (fun y _=>scalar y)]
      simp only [integral_const_mul]
    _ ≤ ∑ y:S,‖w y‖*D₀:=sum_le_sum (fun y _=>mul_le_mul_of_nonneg_left (cost y) (norm_nonneg _))
    _ = (∑y:S,‖w y‖)*D₀ := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalThermometerCells.variation test χ measured) d0

include live in
/-- Only cells carrying a nonzero signed mass need the original local comparison. -/
theorem occupied (test:Test 3) (χ:Points 3 → S) (measured:Measurable χ)
    (Z:S → Config G (R.family.side i per) → ℂ) (D₀:ℝ) (nonneg:0 ≤ D₀)
    (env:∀o,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 → RG.Envelope (Z o))
    (cost:∀o,WilsonSeparatedOriginalThermometerCells.weight test χ o≠0 →
      (∫U,‖Z o U‖ ∂scene R.family.path N per i) ≤ D₀) :
    let result:=fun U=>test.applyTo (fun x=>Z (χ x) U)
    RG.Envelope result ∧ ∀j (age:j ≤ i),
      (∫U,‖actualTransport R.family (N:=N) result age U‖ ∂scene R.family.path N per j) ≤
        (∫x:Points 3,‖test x‖)*D₀ := by
  let w:=WilsonSeparatedOriginalThermometerCells.weight test χ
  let selected:=fun o=>if w o=0 then (fun _:Config G (R.family.side i per)=>(0:ℂ)) else Z o
  have envelope (o:S):RG.Envelope (selected o):=by
    by_cases h:w o=0
    · simpa only [selected,if_pos h] using (RG.Envelope.constC 0)
    · simpa only [selected,if_neg h] using env o h
  have charge (o:S):(∫U,‖selected o U‖ ∂scene R.family.path N per i) ≤ D₀:=by
    by_cases h:w o=0
    · simpa [selected,h] using nonneg
    · simpa only [selected,if_neg h] using cost o h
  have same:(fun U=>test.applyTo (fun x=>Z (χ x) U))=
      fun U=>test.applyTo (fun x=>selected (χ x) U) := by
    funext U
    rw [WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>Z o U),
      WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>selected o U)]
    apply Finset.sum_congr rfl
    intro o _
    change w o*Z o U=w o*selected o U
    by_cases h:w o=0 <;> simp [selected,h]
  simpa only [same] using (tested R live test χ measured selected D₀ envelope charge).2

/-- Both registered clocks receive their own three site residues of the submitted profile. -/
def cells (b per:ℕ) (r:ℝ) (x:Points 3) :=
  (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r ((b+1)+1,per) x,
   WilsonSeparatedOriginalThermometerCells.positions (R:=R) r (b+1,per) x)

theorem measurable_cells (b per:ℕ) (r:ℝ) : Measurable (cells R b per r) :=
  (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r ((b+1)+1,per)).prodMk
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r (b+1,per))

end YM.Integration.WilsonReceivedCompactPriorIntegral
