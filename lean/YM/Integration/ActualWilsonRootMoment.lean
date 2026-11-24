import YM.Integration.ActualWilsonRootDistance
import YM.Integration.SelectedCofactorAnchoredRegister

/-! Absolute Wilson first moment of the complete signed rebooked minor on a physical root window. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualWilsonRootMoment
open Function Filter Set Finset MeasureTheory Lattice Lattice.Corona Wilson RG Marker Source Labels RG3.Script.Picnic
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained Comparison.RG02
open PhysicalNext.Repeat.Legato Extra.Histories SectorNext.Vacuum OPE.Therm OPE.Therm.House Cells
open ActualWilsonRootDistance
open scoped Classical BigOperators Matrix.Norms.Frobenius Topology
variable {G : Gauge} {n : Side}

/-- One root, on the actual torus, measured in the same legs as the support invoice. -/
def zone (o : Site n) (B r : ℕ) : Support n := halo (r*Push.GridApprox.Attach.leg B) {o}

theorem outside {θ : ℝ} {o : Site n} {B r : ℕ} {U : Config G n}
    (h : U∉SelectedCofactorAnchoredRegister.hot θ (zone o B r)) : Remote B θ o r U := by
  intro z hz
  by_contra! less
  exact h ⟨z,halo_spec.mpr ⟨o,mem_singleton_self _,((Nat.div_lt_iff_lt_mul (Push.GridApprox.Attach.leg_pos B)).mp less).le⟩,hz⟩

theorem event {C : Family G} {m N p : ℕ} (hC : C.Makes) (H : SelectedWilsonRootMoment.Hot C m) (hm : m<N)
    {θ : ℝ} (hc : cool C.path.levels m≤θ) (X : Finset (Site (C.side m p))) :
    (scene C.path N p m).real (SelectedCofactorAnchoredRegister.hot θ X) ≤
      ((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*vanishP C.path.levels m := by
  let E := SelectedCofactorAnchoredRegister.hot (G:=G) θ X
  let t := E.indicator (fun _ => (1:ℂ))
  have hE : MeasurableSet E := SelectedCofactorAnchoredRegister.measurable _ _
  have h1 (U) : ‖t U‖≤1 := by by_cases h : U∈E <;> simp [t,h]
  have ht : Envelope t := ⟨measurable_const.indicator hE,1,h1⟩
  have hf (U) (hu : t U≠0) : ∃ z∈X,z∈flags (cool C.path.levels m) U := by
    have he : U∈E := by by_contra h; exact hu (Set.indicator_of_notMem h _)
    obtain ⟨z,hz,hflag⟩ := he
    obtain ⟨p,hp,hp'⟩ := (flags_spec _ _ _).mp hflag
    exact ⟨z,hz,(flags_spec _ _ _).mpr ⟨p,hp,hc.trans_lt hp'⟩⟩
  have b := H N hm p X (fun _ => (1:ℂ)) (fun _ => (0:ℂ)) t
    ⟨measurable_const,1,fun _ => by norm_num⟩ ⟨measurable_const,0,fun _ => by norm_num⟩
    ht h1 hf 1 0 zero_le_one le_rfl (fun _ => by norm_num) (fun _ => by norm_num)
  haveI := probability (H:=C.path) (p:=p) hC.wilson hm.le
  have he : ∫ U,t U ∂scene C.path N p m = ((scene C.path N p m).real E:ℂ) := by
    rw [show t=E.indicator (fun _ => (1:ℂ)) from rfl,integral_indicator hE,setIntegral_const]
    simp
  simpa only [actualAverage_const C hC hm,sub_zero,mul_one,add_zero,he,Complex.norm_real,
    Real.norm_of_nonneg measureReal_nonneg] using b

variable {V : Type} [Fintype V] [DecidableEq V] {B : Census V} (R : Run G) (hG : G.Simple)
    {J : Request V} {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta} {M : AnalyticOutput caps Y K F}
    {δ : ℝ} {a : ℕ}

def fee (F : AnalyticInput J A datum) (a : ℕ) (v : V) := F.kernelCosts v*
  (forcedDivisor R.family datum.level*Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)^a/F.outputRadii v)

def minor (S : Chosen K I M) (x : IndependentTests J.tests) (v : V) (U : Config G (R.family.side datum.level datum.period)) : ℂ :=
  let D := S.output.residual.leaf (testInclusion J.tests x)
  let e := ActualWilsonForcedSlots.address S.output.carrier.rep
    (OriginalForcedAddresses.actual_keeper R hG datum.cutoff datum.level datum.period datum.below.le)
  ∑' j, (D.contents.each j U).part (B.fire v)*dressed (R.family.path.rep datum.cutoff datum.period datum.level) (e j) U

theorem measurable (S : Chosen K I M) (H : Bounds S δ a)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent≤J.outputSupport)
    (x : IndependentTests J.tests) (v : V) : Measurable (minor R hG S x v) := by
  let D := S.output.residual.leaf (testInclusion J.tests x)
  obtain ⟨q,_,_,hq,hformat,_⟩ := ActualWilsonResidualCoefficient.selected S H v hreserve x
  have hy (j : ℕ) : (fun U => (D.contents.each j U).part (B.fire v))=q.forced j := by
    funext U
    rw [hq]
    exact ActualWilsonForcedRow.each_solution D v j U (SelectedCofactorSupportBudget.tagged_summable H.residual_price F.kernel_positive x j U)
  apply Measurable.tsum
  intro j
  exact ((hy j) ▸ hformat.borel j).mul (dressed_meas (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good _)

theorem window (S : Chosen K I M) (H : Bounds S δ a)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent≤J.outputSupport)
    (hot : SelectedWilsonRootMoment.Hot R.family datum.level)
    (hc : cool R.family.path.levels datum.level≤S.output.carrier.rep.p.threshold)
    (x : IndependentTests J.tests) (v : V) (r : ℕ) :
    let p := A.outputNorm datum.level
    let X := zone (F.coarseRoots v) p.B r
    let μ := scene R.family.path datum.cutoff datum.period datum.level
    ∫ U,‖minor R hG S x v U‖ ∂μ ≤
      (((X.card*(Fintype.card PlaqAxes*4):ℕ):ℝ)*vanishP R.family.path.levels datum.level+
       Real.exp (-p.supportExponent*r))*fee R F a v := by
  intro p X μ
  let E := SelectedCofactorAnchoredRegister.hot (G:=G) S.output.carrier.rep.p.threshold X
  let B := fee R F a v
  let d := Real.exp (-p.supportExponent*r)*B
  have hB : 0≤B := by
    dsimp only [B,fee]
    have hg := IterationFour.Currency.g_pos R.makes datum.cutoff datum.period (datum.level+1) datum.below
    exact mul_nonneg (F.kernel_positive v).le (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hg.le _)) (F.output_radius_positive v).le)
  have hd : 0≤d := mul_nonneg (Real.exp_pos _).le hB
  have hE : MeasurableSet E := SelectedCofactorAnchoredRegister.measurable _ _
  haveI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=datum.period) R.makes.wilson datum.below.le
  have cheap (U) : ‖minor R hG S x v U‖≤B := by
    have h := (ActualWilsonRootDistance.wilson R hG S H hreserve x v U 0 (fun _ _ => Nat.zero_le _)).2
    simpa only [minor,B,fee,Nat.cast_zero,mul_zero,Real.exp_zero,one_mul] using h
  have hid : Integrable (fun U => ‖minor R hG S x v U‖) μ := Integrable.of_bound
    (measurable R hG S H hreserve x v).norm.aestronglyMeasurable B (ae_of_all _ fun U => by
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using cheap U)
  have ih : Integrable (E.indicator (fun _ => B)) μ := (integrable_const _).indicator hE
  have id' : Integrable (fun _ : Config G (R.family.side datum.level datum.period) => d) μ := integrable_const _
  have he := event R.makes hot datum.below hc X (p:=datum.period)
  calc
    _ ≤ ∫ U,E.indicator (fun _ => B) U+d ∂μ := by
      apply integral_mono hid (ih.add id')
      intro U
      change ‖minor R hG S x v U‖ ≤ E.indicator (fun _ => B) U+d
      by_cases hu : U∈E
      · rw [Set.indicator_of_mem hu]
        exact (cheap U).trans (le_add_of_nonneg_right hd)
      · rw [Set.indicator_of_notMem hu,zero_add]
        exact (ActualWilsonRootDistance.wilson R hG S H hreserve x v U r (outside hu)).2
    _ = μ.real E*B+d := by rw [integral_add ih id',integral_indicator hE,setIntegral_const,integral_const];simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right he hB
      dsimp only [d]
      rw [add_mul]
      exact add_le_add h le_rfl

end YM.Integration.ActualWilsonRootMoment
