import YM.Integration.WilsonPhysicalHistoryKioskPlaquettes
import YM.Integration.PhysicalWilsonHotAllowance
import YM.Integration.ActualWilsonAbsoluteTransport

/-! Integrate the signed collar change with its original Wilson detector.
The radius is allowed to grow after the starting date has been fixed. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPhysicalHistoryKioskHeat
open Function Filter Set Finset Lattice Wilson RG OPE.Therm Push.AbsoluteSums.Animals
open MeasureTheory IterationFour PhysicalNext.Repeat.Legato
open scoped Topology Classical BigOperators

private theorem fraction {x : ℝ} (pos : 0<x) (unit : x≤1) (f : ℕ) :
    ((Real.sqrt x)^f)⁻¹*x^(f+1) ≤ x := by
  let u := Real.sqrt x
  have hu : 0<u := Real.sqrt_pos.mpr pos
  have low : u≤1 := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt unit
  have twice : x=u*u := (Real.mul_self_sqrt pos.le).symm
  have powers : x^f=u^f*u^f := by rw [←mul_pow,←twice]
  have equal : (u^f)⁻¹*x^(f+1)=x*u^f := by
    rw [pow_succ,powers]
    field_simp [hu.ne']
  rw [show ((Real.sqrt x)^f)⁻¹*x^(f+1) = x*u^f from equal]
  exact mul_le_of_le_one_right pos.le (pow_le_one₀ hu.le low)

private theorem indicator_price {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {E : Set X} {F : X → ℂ} {b : ℝ} (meas : MeasurableSet E)
    (hF : Measurable F) (cap : ∀ x, ‖F x‖≤b) (support : ∀ x, x∉E → F x=0) :
    ∫ x, ‖F x‖ ∂μ ≤ b*μ.real E := by
  have integ : Integrable F μ :=
    Integrable.of_bound hF.aestronglyMeasurable b (ae_of_all _ cap)
  have inside (x) : ‖F x‖≤ E.indicator (fun _=>b) x := by
    by_cases live : x∈E
    · simpa [live] using cap x
    · simp [live,support x live]
  apply (integral_mono integ.norm ((integrable_const b).indicator meas) inside).trans_eq
  rw [integral_indicator meas,setIntegral_const]
  simp [smul_eq_mul,mul_comm]

variable {G : Gauge} (R : Run G) (simple : G.Simple) (temperatures : Poetry R.family.path.levels)
local notation "κ" => R.family.path.levels.clock.forcedAllowance

include simple temperatures in
theorem measured (f : ℕ) :
    ∀ᶠ i : ℕ in atTop, ∀ N, i≤N → ∀ per H (x : Site (R.family.side i per)),
      ∀ F J : Config G (R.family.side i per) → ℂ, Measurable F → Measurable J →
      (∀ U, Healthy (R.family.path.rep N per i).p.threshold (neighbors (H+H) x) U → F U=0) →
      (∀ U, ‖F U‖ * (ballCost H:ℝ) ≤ 1) →
      ∀ b : ℝ, (∀ U, ‖J U‖ ≤ b) → ∀ j (hj : j ≤ i),
      ∫ V, ‖actualTransport R.family (N:=N) (p:=per)
        (fun U => ((Real.sqrt (κ i))^f)⁻¹ • (J U * F U)) hj V‖
        ∂scene R.family.path N per j ≤ b*(625*(Fintype.card PlaqAxes:ℝ))*κ i := by
  let D : ℝ := 625*(Fintype.card PlaqAxes:ℝ)
  have dn : 0≤D := by dsimp [D]; positivity
  filter_upwards [PhysicalWilsonHotAllowance.faces temperatures simple R.makes.wilson
    (ρ:=1) zero_lt_one (f+1)] with i thermal N dated per H x F J hmF hmJ healthy salary b probe j hj
  letI : IsProbabilityMeasure (scene R.family.path N per i) := OPE.Therm.probability (p:=per) R.makes.wilson dated
  let vacancies := WilsonPhysicalHistoryKioskPlaquettes.faces H x
  let hot := (House.chilly (G:=G) vacancies (R.family.path.rep N per i).p.threshold)ᶜ
  let L : ℝ := ballCost H
  let h := ((Real.sqrt (κ i))^f)⁻¹
  let read := fun U => h • (J U * F U)
  have lpos : 0<L := by dsimp [L,ballCost]; positivity
  have bn : 0≤b := (norm_nonneg (J 1)).trans (probe 1)
  have wn : 0<κ i := Real.exp_pos _
  have unit : κ i≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_nonneg _) _))
  have hn : 0≤h := by dsimp [h]; positivity
  have thermalCut : (scene R.family.path N per i).real hot ≤
      vacancies.card*(κ i)^(f+1) := by
    simpa only [one_mul,hot] using thermal N dated per vacancies
  have count : (vacancies.card : ℝ) ≤ L*D := by
    have hc := WilsonPhysicalHistoryKioskPlaquettes.count H x
    change (vacancies.card : ℝ) ≤ (ballCost H:ℝ)*(625*(Fintype.card PlaqAxes:ℝ))
    rw [show (ballCost H:ℝ)*(625*(Fintype.card PlaqAxes:ℝ)) =
      625*(ballCost H:ℝ)*(Fintype.card PlaqAxes:ℝ) by ring]
    exact_mod_cast hc
  have small (U) : ‖F U‖ ≤ L⁻¹ := by
    rw [←one_div]
    exact (le_div_iff₀ lpos).mpr (salary U)
  have measurable : Measurable read := (measurable_const (a:=h)).smul (hmJ.mul hmF)
  have cap (U) : ‖read U‖ ≤ h*(b*L⁻¹) := by
    change ‖h • (J U*F U)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg hn,norm_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_mul (probe U) (small U) (norm_nonneg _) bn) hn
  have support (U) (cool : U∉hot) : read U=0 := by
    have calm : U∈House.chilly vacancies (R.family.path.rep N per i).p.threshold := by simpa [hot] using cool
    simp [read,healthy U (WilsonPhysicalHistoryKioskPlaquettes.healthy H x U calm)]
  have measured := indicator_price (μ:=scene R.family.path N per i)
    (House.bath vacancies).compl measurable cap support
  have weighted := ActualWilsonAbsoluteTransport.weighted R.family R.makes dated
    (show Envelope read from ⟨measurable,h*(b*L⁻¹),cap⟩)
  calc
    _ ≤ ∫ U, ‖read U‖ ∂scene R.family.path N per i := ActualWilsonAbsoluteTransport.first
      R.family R.makes dated weighted hj
    _ ≤ (h*(b*L⁻¹))*(scene R.family.path N per i).real hot := measured
    _ ≤ (h*(b*L⁻¹))*((L*D)*(κ i)^(f+1)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hn (mul_nonneg bn (inv_nonneg.mpr lpos.le)))
      exact thermalCut.trans (mul_le_mul_of_nonneg_right count (pow_nonneg wn.le _))
    _ = b*D*(h*(κ i)^(f+1)) := by field_simp [lpos.ne']
    _ ≤ b*D*(κ i) := mul_le_mul_of_nonneg_left (fraction wn unit f) (mul_nonneg bn dn)

end YM.Integration.WilsonPhysicalHistoryKioskHeat
end
