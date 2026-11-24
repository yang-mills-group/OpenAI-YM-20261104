import YM.Integration.ActualWilsonSpectatorBudget
import YM.Integration.ActualRunCoarseReadout
import YM.OPE.Therm.Law

/-! The signed spectator on the original normalized Wilson scene. Both
vacuum divisors and the dirty support of the retained row remain explicit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSpectatorReadout

open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Labels
open Extra.Histories Relay Bid RG3.Script.Picnic RG3.Forms
open Comparison.RG02 LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato OPE.Therm
open ActualWilsonGraphReclosure ActualWilsonForcedSlots ActualWilsonAxisSpectator
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

private theorem coat_borel {P : Rep G n} (h : ∀ j, Measurable (P.activities.K j)) (i : ℕ) (s : Finset ℕ) :
    Measurable (coat P i s) := by
  classical
  by_cases hi : i ∈ s
  · unfold coat
    simp only [hi,true_and]
    exact Measurable.ite (P.activities.admissible_borel P.p s)
      (Finset.measurable_fun_prod _ fun j _ => Complex.continuous_ofReal.measurable.comp (h j))
      measurable_const
  unfold coat
  simp only [hi,false_and,if_false]
  exact measurable_const

private theorem dressed_borel {P : Rep G n} (h : ∀ j, Measurable (P.activities.K j)) (i : ℕ) :
    Measurable (dressed P i) := Measurable.tsum (coat_borel h i)

variable (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F} {δ : ℝ} {a : ℕ}

local notation "W" => R.family.path.rep datum.cutoff datum.period datum.level
local notation "μ₀" => prior G (R.family.side datum.level datum.period)
local notation "Z₀" => partition G (R.family.side datum.cutoff datum.period)
  (R.family.path.β datum.cutoff datum.period datum.cutoff)
local notation "Fee" v => forcedDivisor R.family datum.level *
  (F.kernelCosts v * (Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)) ^ a / F.outputRadii v)

def row (S : Chosen K I M) (x : IndependentTests J.tests) (v : V) (j : ℕ)
    (U : Config G (R.family.side datum.level datum.period)) : ℂ :=
  ((S.output.residual.leaf (testInclusion J.tests x)).contents.each j U).part (B.fire v)

def normalized (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (U : Config G (R.family.side datum.level datum.period)) : ℂ :=
  ((W).eval U : ℂ)⁻¹ * spectator R hG S x v U

def dirty (S : Chosen K I M) : Set (Config G (R.family.side datum.level datum.period)) :=
  {U | flags S.output.carrier.rep.p.threshold U ≠ ∅}

theorem dirty_measurable (S : Chosen K I M) : MeasurableSet (dirty R S) :=
  (flags_measurable_eq S.output.carrier.rep.p.threshold ∅).compl

private theorem native_rows (S : Chosen K I M) (H : Bounds S δ a) (x : IndependentTests J.tests)
    (v : V) (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport) :
    ∃ q : Coefficient (R.family.labels.level (J.outputWeight v)) (R.family.side datum.level datum.period),
      (∀ j, q.forced j = row R S x v j) ∧
      q.Format (F.coarseRoots v) R.family.params S.output.carrier.rep ∧
      q.remBound (F.coarseRoots v) S.output.carrier.rep (forcedDivisor R.family datum.level)
        (F.kernelCosts v * (Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)) ^ a / F.outputRadii v) := by
  obtain ⟨q,_,_,he,hf,hb⟩ := ActualWilsonResidualCoefficient.selected S H v hreserve x
  refine ⟨q,?_,hf,hb⟩
  intro j
  funext U
  rw [he]
  exact (ActualWilsonForcedRow.each_solution _ v j U
    (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U)).symm

/-- A selected forced coefficient can contribute only on its demanded
native inventory. In particular the whole signed comparison vanishes off
the original dirty event. -/
theorem clean (S : Chosen K I M) (H : Bounds S δ a) (x : IndependentTests J.tests) (v : V)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (U : Config G (R.family.side datum.level datum.period)) (hc : U ∉ dirty R S) :
    spectator R hG S x v U = 0 := by
  have hd : flags S.output.carrier.rep.p.threshold U = ∅ := by
    simpa only [dirty,mem_setOf_eq,not_not] using hc
  obtain ⟨q,hq,hf,_⟩ := native_rows R S H x v hreserve
  have hz (j : ℕ) : row R S x v j U = 0 := by
    rw [← hq j]
    by_contra hn
    have hit := (hf.forcing j U hn).1
    rw [hd,Finset.inter_empty] at hit
    exact (S.output.carrier.rep.activities.forced j).inventory_ne.ne_empty hit.symm
  unfold spectator
  apply (tsum_congr (g := fun _ : ℕ => (0 : ℂ)) (fun j => mul_eq_zero_of_left (hz j) _)).trans
  exact tsum_zero

private theorem cancel_exponential (P Q : Rep G n) (U : Config G n)
    (h : P.eval U = Q.eval U) :
    (Q.eval U : ℂ)⁻¹ * (Real.exp (P.exponent U) : ℂ) =
      (P.activities.gas P.p U : ℂ)⁻¹ := by
  rw [←h]
  change ((Real.exp (P.exponent U) * P.activities.gas P.p U : ℝ) : ℂ)⁻¹ * _ = _
  rw [Complex.ofReal_mul,mul_inv_rev,mul_assoc,inv_mul_cancel₀
    (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),mul_one]

/-- Full normalization retains the difference of the two conditional
minors inside each signed row. -/
theorem conditional_rows (S : Chosen K I M)
    (hFine : I.carrier.rep.eval = (R.family.path.rep datum.cutoff datum.period (datum.level+1)).eval)
    (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) :
    let X := S.output.carrier.rep
    let e := address X (OriginalForcedAddresses.actual_keeper R hG datum.cutoff datum.level datum.period datum.below.le)
    normalized R hG S x v U = ∑' j, row R S x v j U *
      ((X.activities.gas X.p U : ℂ)⁻¹ * dressed X j U -
        ((W).activities.gas (W).p U : ℂ)⁻¹ * dressed W (e j) U) := by
  intro X e
  have hx := cancel_exponential X W U (congrFun (S.output.output_vacuum R.makes datum.below hFine) U)
  have hw := cancel_exponential W W U rfl
  unfold normalized spectator
  rw [←tsum_mul_left]
  apply tsum_congr
  intro j
  change _ * (row R S x v j U * (_ - _)) = _
  rw [←hx,←hw]
  ring

/-- Multiplication by an arbitrary original test commutes with density
clearing. The partition is the fine Wilson partition at this very cutoff. -/
theorem projection (S : Chosen K I M) (x : IndependentTests J.tests) (v : V)
    (φ : Config G (R.family.side datum.level datum.period) → ℂ) :
    (∫ U, φ U * normalized R hG S x v U ∂scene R.family.path datum.cutoff datum.period datum.level) =
      (Z₀ : ℂ)⁻¹ * ∫ U, φ U * spectator R hG S x v U ∂μ₀ := by
  rw [violet (H:=R.family.path) (p:=datum.period) R.makes.wilson datum.below.le,div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro U
  have hpos := (ActualCoveredNormalization.same_run_reference R datum.cutoff datum.period datum.level datum.below.le).1 U
  unfold normalized
  have hn : ((W).eval U : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  field_simp

theorem measurable (S : Chosen K I M) (H : Bounds S δ a) (x : IndependentTests J.tests) (v : V)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport) :
    Measurable (spectator R hG S x v) := by
  obtain ⟨q,hq,hf,_⟩ := native_rows R S H x v hreserve
  have hW := (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good
  have hX := (ActualSelectedModelEnvelope.chosen_exponent_envelope R.makes S).exp.meas
  unfold spectator
  apply Measurable.tsum
  intro j
  exact ((hq j) ▸ hf.borel j).mul
    (((Complex.continuous_ofReal.measurable.comp hX).mul (dressed_borel S.wellFormed.forced.meas j)).sub
      ((Complex.continuous_ofReal.measurable.comp ((W).exponentEnv hW).exp.meas).mul (dressed_meas hW _)))

/-- Only the mass of dirty original fields enters the normalized Wilson
projection, against both actual exponentials and the original fine partition. -/
theorem dirty_projection (S : Chosen K I M) (H : Bounds S δ a)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) (v : V)
    (φ : Config G (R.family.side datum.level datum.period) → ℂ) (hφ : Envelope φ) :
    let X := S.output.carrier.rep
    let c := Fee v
    let m := fun U => (dirty R S).indicator
      (fun T => ‖φ T‖ * (Real.exp (X.exponent T) + Real.exp ((W).exponent T))) U
    Integrable (fun U => φ U * spectator R hG S x v U) μ₀ ∧
      ‖∫ U, φ U * normalized R hG S x v U ∂scene R.family.path datum.cutoff datum.period datum.level‖ ≤
        Z₀⁻¹ * ((∫ U, m U ∂μ₀) * c) := by
  intro X c m
  have hW := (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good
  have hX := (ActualSelectedModelEnvelope.chosen_exponent_envelope R.makes S).exp
  have hsum := hX.add ((W).exponentEnv hW).exp
  obtain ⟨b,hb⟩ := hφ.cost
  have hmφ : Envelope (fun U => ‖φ U‖) :=
    ⟨hφ.meas.norm,b,fun U => (Real.norm_of_nonneg (norm_nonneg _)).trans_le (hb U)⟩
  have hI : Integrable m μ₀ := ((hmφ.mul hsum).integrable μ₀).indicator (dirty_measurable R S)
  have hg := (measurable R hG S H x v hreserve)
  have hpay (U) : ‖φ U * spectator R hG S x v U‖ ≤ m U*c := by
    by_cases hd : U ∈ dirty R S
    · rw [norm_mul]
      change _ ≤ (dirty R S).indicator _ U * _
      rw [Set.indicator_of_mem hd,mul_assoc]
      exact mul_le_mul_of_nonneg_left (ActualWilsonSpectatorBudget.selected R hG S H hLate hreserve x v U).2 (norm_nonneg _)
    change _ ≤ (dirty R S).indicator _ U * _
    rw [Set.indicator_of_notMem hd,zero_mul,clean R hG S H x v hreserve U hd,mul_zero,norm_zero]
  have hf := (hI.mul_const c).mono' (hφ.meas.mul hg).aestronglyMeasurable (Eventually.of_forall hpay)
  refine ⟨hf,?_⟩
  rw [projection R hG S x v φ,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (partition_pos _).le]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (partition_pos _).le)
  have hl := (norm_integral_le_integral_norm _).trans (integral_mono hf.norm (hI.mul_const c) hpay)
  rwa [integral_mul_const] at hl

end YM.Integration.WilsonSpectatorReadout
