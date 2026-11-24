import YM.Integration.SelectedCofactorLocalProjection
import YM.Integration.LocalComparisonForcedCover
import YM.Integration.WilsonSpectatorReflection
import YM.Push.SECTOR_MEASURE.Decompose
import YM.UVNext.COUPLING_RESET.Probe

/-! Integrability of the genuine marked fine source follows from one
nonzero active clean output of the original strictly positive Wilson step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PositiveWilsonMarkedInput

open Function Finset Set MeasureTheory Lattice Wilson RG Marker Overlay RG3.Forms
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained RG3.Script.Picnic
open scoped Classical BigOperators Topology

variable {G : Gauge} {n c f : Side} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}

omit [Fintype V] in
private theorem quiet_series (a : ℕ → Poly B) (h : ∀ j, (a j).part B.quiet = 0) :
    (∑' j, a j).part B.quiet = 0 := by
  by_cases hs : Summable a
  · rw [Poly.share hs]
    simp only [h,tsum_zero]
  · simp [tsum_eq_zero_of_not_summable hs]

/-- Every structurally active selected Deck has zero quiet logarithm;
each individual caption, global term, and marked regular row has nonempty mode. -/
theorem quiet_log {P : Rep G n} (d : Deck B P) (hd : d.Active) (U : Config G n) :
    (d.log U).part B.quiet = 0 := by
  have hp {s : B.Mode} (hs : s.val.Nonempty) (z : ℂ) :
      (Poly.send s z).part B.quiet = 0 := by
    rw [Poly.part_send,if_neg (fun h => hs.ne_empty (congrArg Subtype.val h.symm))]
  have hR := quiet_series (fun i => d.contents.ray i U) (fun i => hp (hd.articles.proper i) _)
  have hC := quiet_series (fun i => Poly.send (d.captions.tag i) (d.captions.value i))
    (fun i => hp (hd.captions.card i) _)
  simp only [Deck.log,Poly.part_plus,Bands.extra,Captions.chord,Poly.part_sum,hR,hC,add_zero,
    Poly.part_send,if_neg (B.fire_hot _).symm,sum_const_zero]

/-- At every clean field the full active marked polynomial has its
strictly positive, actual exponential as quiet coefficient. -/
theorem clean {P : Rep G n} (d : Deck B P) (hd : d.Active) (U : Config G n)
    (hU : flags P.p.threshold U = ∅) : (d.density U).part B.quiet = (Real.exp (P.exponent U) : ℂ) := by
  have hCl : d.contents.cluster U = 1 := by
    have hh := sub_eq_zero.mp (forcedClusterError_zero d U hU)
    simpa only [P.activities.gas_one P.p hU,Complex.ofReal_one,one_smul] using hh
  rw [Deck.density,Poly.part_smul,hCl,mul_one,Poly.pass_part _ (quiet_log d hd U)]
  simp

private theorem original_floor (S : StepData c f) (h : S.patch.Branches S.kernel G) (b : ℝ)
    (U : Config G f) (V₀ : Config G c) : (Push.BetaTransport.noiseCost S |b|)⁻¹ ≤ S.density b U V₀ := by
  let a := (Push.BetaTransport.noiseCost S |b|)⁻¹
  calc a = ∑ t, S.likelihood U t * a := by rw [←sum_mul,S.chosen h,one_mul]
       _ ≤ _ := sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
         (Push.BetaTransport.noise_bounds S (le_refl |b|) (S.prediction U t) V₀).1 (S.likelihood_pos U t)

private theorem invert_slice {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure X} (d : X → ℝ) (g : X → E) (hm : Measurable d) {a : ℝ} (ha : 0 < a)
    (hl : ∀ U, a ≤ d U) (hi : Integrable (fun U => d U • g U) μ) : Integrable g μ := by
  have hinv : Envelope (fun U => (d U)⁻¹) := ⟨hm.inv,a⁻¹,fun U =>
    (Real.norm_of_nonneg (inv_nonneg.mpr (ha.trans_le (hl U)).le)).trans_le (inv_anti₀ ha (hl U))⟩
  have hI := Push.SectorMeasure.Env.smul_L1 (μ:=μ) (H:=fun U => (d U)⁻¹) (f:=fun U => d U • g U) hinv hi
  apply hI.congr
  apply ae_of_all
  intro U
  change (d U)⁻¹ • (d U • g U) = g U
  rw [smul_smul,inv_mul_cancel₀ (ha.trans_le (hl U)).ne',one_smul]

private theorem density_meas (S : StepData c f) (h : S.patch.Branches S.kernel G) (b : ℝ) (V₀ : Config G c) :
    Measurable (fun U : Config G f => S.density b U V₀) := by
  have hpair : Measurable (fun U : Config G f => (U,V₀)) := measurable_id.prodMk measurable_const
  exact Measurable.comp (g:=fun p : Config G f × Config G c => S.density b p.1 p.2)
    (f:=fun U : Config G f => (U,V₀)) (S.isKernel h b).meas hpair

private theorem nonzero_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : StepData c f)
    (b : ℝ) (g : Config G f → E) (V₀ : Config G c) (hn : S.push b g V₀ ≠ 0) :
    Integrable (fun U : Config G f => S.density b U V₀ • g U) (prior G f) := by
  by_contra hnil
  apply hn
  unfold StepData.push
  exact integral_undef hnil

/-- A nonzero true positive Wilson push at any actual output field forces
integrability of its original signed source by bounded kernel inversion. -/
theorem of_push {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : StepData c f)
    (h : S.patch.Branches S.kernel G) (b : ℝ) (g : Config G f → E) (V₀ : Config G c)
    (hn : S.push b g V₀ ≠ 0) : Integrable g (prior G f) :=
  invert_slice (μ:=prior G f) (fun U => S.density b U V₀) g (density_meas S h b V₀)
    (a:=(Push.BetaTransport.noiseCost S |b|)⁻¹) (inv_pos.mpr (Push.BetaTransport.noiseCost_pos S _))
    (fun U => original_floor S h b U V₀) (nonzero_slice S b g V₀ hn)

variable {J : Request V} {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}

/-- An original Chosen output already forces its complete fine marked
input to be integrable for every test, through its actual clean quiet component. -/
theorem selected (S : Chosen K I M) (x : TestSpace J.tests) :
    Integrable (I.input.leaf x).density (prior G (C.side (datum.level+1) datum.period)) := by
  let k := C.path.levels.clock.op datum.level datum.period
  let b := C.path.β datum.cutoff datum.period (datum.level+1)
  apply of_push k (C.path.levels.blocks datum.level datum.period).branches b _ 1
  change actualPush C datum.cutoff datum.period datum.level (I.input.leaf x).density 1 ≠ 0
  rw [S.output.density x]
  intro hz
  have hp := clean (S.output.output.leaf x) (S.output_active x) 1 (UVNext.CouplingReset.flags_one _)
  rw [hz] at hp
  exact (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') hp.symm

end YM.Integration.PositiveWilsonMarkedInput
