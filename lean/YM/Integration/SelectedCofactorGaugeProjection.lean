import YM.Integration.SelectedCofactorLocalProjection
import YM.Next.RANK.Determinant
import YM.OPE.Therm.Law

/-! Gauge averaging of the local signed marginal on the original Wilson scene. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedCofactorGaugeProjection
open Function Finset Set Filter MeasureTheory Lattice Wilson RG Marker Overlay Cells
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.RenderedStep.Numeric.Retained RG3.Forms RG3.Script.Picnic OPE.Therm
open NativeTasteCoveredCofactor NativeCoveredCofactorLocalUpdate
open SelectedCofactorConditionalSeries SelectedCofactorReplicatedFlags SelectedCofactorLocalProjection
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}

def orbit (f : Config G n → ℂ) (U : Config G n) : ℂ :=
  ∫ g, f (gauge g U) ∂Measure.pi (fun _ : Site n => G.probHaar)

private theorem action_meas :
    Measurable (fun z : Config G n × (Site n → G.El) => gauge z.2 z.1) := by unfold Lattice.gauge; fun_prop

theorem interior (X : Set (Site n)) {f : Config G n → ℂ} (hf : Envelope f) (hX : LocalOn X f) :
    Interior X (orbit f) := by
  let J := Measure.pi (fun _ : Site n => G.probHaar)
  have hme := (hf.meas.comp (action_meas (G := G) (n := n))).stronglyMeasurable
  obtain ⟨b,hb⟩ := hf.cost
  refine ⟨fun k U => ?_,(hme.integral_prod_right' (ν := J)).measurable,fun U V h => ?_,b,fun U => ?_⟩
  · let E := MeasurableEquiv.piCongrRight (fun z => MeasurableEquiv.mulRight (k z))
    have h : MeasurePreserving E J J := measurePreserving_pi _ _ fun i : Site n => measurePreserving_mul_right ..
    unfold orbit
    rw [← h.integral_comp' (fun g => f (gauge g U))]
    apply integral_congr_ae
    apply ae_of_all
    intro g
    apply congrArg f
    funext e
    unfold Lattice.gauge
    change _ = (g _*k _)*U _*(g _*k _)⁻¹
    group
  · exact integral_congr_ae (ae_of_all _ fun g => hX _ _ (fun e hx hy => by unfold Lattice.gauge; rw [h e hx hy]))
  · simpa only [orbit,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ := J) (C := b) (ae_of_all _ fun g => hb (gauge g U))

theorem unchanged {P : Config G n → ℝ} {f : Config G n → ℂ} (hP : Envelope P)
    (hF : Envelope f) (hG : GaugeInvariant P) :
    (∫ U, P U • orbit f U ∂prior G n) = ∫ U, P U • f U ∂prior G n := by
  let J := Measure.pi (fun _ : Site n => G.probHaar)
  let μ := prior G n
  haveI : IsProbabilityMeasure μ := inferInstanceAs (IsProbabilityMeasure (Measure.pi (fun _ : Edge (Site n) => G.probHaar)))
  haveI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Edge (Site n) => G.probHaar)))
  haveI : SFinite μ := inferInstanceAs (SFinite (Measure.pi (fun _ : Edge (Site n) => G.probHaar)))
  haveI : IsFiniteMeasure J := inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : Site n => G.probHaar)))
  haveI : SFinite J := inferInstanceAs (SFinite (Measure.pi (fun _ : Site n => G.probHaar)))
  obtain ⟨a,ha⟩ := hP.cost
  obtain ⟨b,hb⟩ := hF.cost
  let q (U : Config G n) (g : Site n → G.El) := P U • f (gauge g U)
  have henv : Envelope (uncurry q) := ⟨(hP.meas.comp measurable_fst).smul (hF.meas.comp action_meas),a*b,
    fun z => (norm_smul_le ..).trans (mul_le_mul (ha z.1) (hb _) (norm_nonneg _) ((norm_nonneg _).trans (ha z.1)))⟩
  have hi := (integrable_const (μ := μ.prod J) henv.cost.choose).mono' henv.meas.aestronglyMeasurable (ae_of_all _ henv.cost.choose_spec)
  have one (g : Site n → G.El) : ∫ U, q U g ∂μ = ∫ U, P U • f U ∂μ := by
    have hpr := prior_gauge g
    have hm : Measurable (fun U => P U • f U) := hP.meas.smul hF.meas
    calc _ = ∫ U, P (gauge g U) • f (gauge g U) ∂μ :=
           integral_congr_ae (ae_of_all _ fun U => congrArg (fun r : ℝ => r • f (gauge g U)) (hG g U).symm)
         _ = ∫ U, P U • f U ∂Measure.map (gauge g) μ :=
           (integral_map hpr.aemeasurable hm.aestronglyMeasurable).symm
         _ = _ := by rw [hpr.map_eq]
  calc _ = ∫ U, ∫ g, q U g ∂J ∂μ :=
         integral_congr_ae (ae_of_all _ fun U => (integral_smul (P U) (fun g => f (gauge g U))).symm)
       _ = ∫ g, ∫ U, q U g ∂μ ∂J := integral_integral_swap hi
       _ = _ := by simp only [one,integral_const,probReal_univ,one_smul,μ]

variable {V : Type} [DecidableEq V] [Fintype V] {B : Census V} {J : Request V}
variable {C : Family G} {A : NumericSchedule C J} {datum : LocalFormal.Datum C B}
    {caps : Handoff.OutputCapacities} {Y : Comparison.RG02.Bulk.Chain C.path}
    {K : NumericPrices A} {F : AnalyticInput J A datum} {eta_w : ℝ}
    {I : FullPreparedInputAt F eta_w} {M : AnalyticOutput caps Y K F} {delta : ℝ} {order : ℕ}

local notation "n₀" => C.side datum.level datum.period
local notation "W₀" => C.path.rep datum.cutoff datum.period datum.level
local notation "Z₀" => partition G (C.side datum.cutoff datum.period) (C.path.β datum.cutoff datum.period datum.cutoff)

/-- One genuine local gauge-invariant observable on the original thermal
scene represents the full original signed packet group. Every nonzero
reading retains a physical local flag. -/
theorem selected (hC : C.Makes) (S : Chosen K I M) (H : Bounds S delta order)
    (x : IndependentTests J.tests) (A₀ X : Set (Site n₀)) (hX : X ⊆ deep A₀)
    (Q : (ℕ × Finset ℕ) → Prop) (L : Poly B →L[ℂ] ℂ) :
    let f := orbit (readout S x A₀ X Q L)
    Interior A₀ f ∧ (∀ t ≤ S.output.carrier.rep.p.threshold, ∀ U, f U ≠ 0 → ∃ z ∈ X, z ∈ flags t U) ∧
      (∫ U, f U ∂scene C.path datum.cutoff datum.period datum.level) =
        (Z₀ : ℂ)⁻¹ * ∫ U, L (rooted S x X Q U) ∂prior G n₀ := by
  obtain ⟨hl,he,hm⟩ := realization hC S H x A₀ X Q L
  let f := readout S x A₀ X Q L
  have hw := (hC.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good
  have hP := (W₀).envelope hw
  have hg := Next.Rank.gauge_eval hw
  have hpair := (unchanged (f := f) hP he hg).trans hm
  refine ⟨interior A₀ he hl,?_,?_⟩
  · intro t ht U hn
    by_contra hz
    apply hn
    have hzero (g : Site n₀ → G.El) : f (gauge g U) = 0 := by
      by_contra h
      obtain ⟨z,hzx,hzf⟩ := hot S x A₀ X hX Q L ht (gauge g U) h
      exact hz ⟨z,hzx,by simpa only [gauge_flags] using hzf⟩
    change (∫ g, f (gauge g U) ∂Measure.pi (fun _ : Site n₀ => G.probHaar)) = 0
    simp only [hzero,integral_zero]
  · rw [violet (H := C.path) (p := datum.period) hC.wilson datum.below.le,div_eq_inv_mul]
    apply congrArg ((Z₀:ℂ)⁻¹ * ·)
    simpa only [Complex.real_smul] using hpair

end YM.Integration.SelectedCofactorGaugeProjection
end
