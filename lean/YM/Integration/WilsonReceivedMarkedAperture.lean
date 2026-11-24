import YM.Integration.WilsonReceivedMarkedCofactor

/-! Read the older regular marked correction with the true positive tagged
Wilson probability on each selected aperture and the original normalization. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReceivedMarkedAperture
open Function Filter Finset MeasureTheory Lattice RG Wilson Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open Actual Order Push.SectorMeasure WilsonOriginalSignedForestAperture
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {ι : Type} [DecidableEq ι] [Fintype ι] {Γ : Census ι}

omit [Fintype ι] in
private theorem norm_charge {α : Type*} [MeasurableSpace α] (μ : Measure α) (w : ι→ℝ)
    (hw : ∀ i,0<w i) (Y : α→Poly Γ) (hy : Good μ Y) :
    Poly.price w (charge μ Y) ≤ ∫ a,Poly.price w (Y a) ∂μ := by
  unfold Poly.price
  rw [integral_finsetSum _ (fun s _ => (hy s).norm.const_mul (Poly.toll w s))]
  apply Finset.sum_le_sum
  intro s _
  rw [components,integral_const_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (Poly.worth hw s).le

variable (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "P₁" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
local notation "Coarse" => Config G (R.family.side d.level d.period)
set_option quotPrecheck false in
local notation "β" => (P₁).beta

omit [Fintype ι] in
private theorem total (F : Forest (Δ).ratio) (V : Coarse) :
    ∑ t : (Δ).Choices,∫ a, Normal.view (Δ) (β) V t (P₁).eval (F.drape a) ∂F.order G =
      (P₀).eval V := by
  have hp := Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below
  have hb := (R.family.path.levels.blocks d.level d.period).branches
  calc
    _ = ∑ t : (Δ).Choices,Normal.mass (Δ) (β) V t (P₁).eval := by
      apply Finset.sum_congr rfl
      intro t _
      symm
      apply F.pack _ ((Normal.view_bound (Δ) (β) V t (P₁).eval hp hb).integrable _)
      intro k hk U
      unfold Normal.view taggedKernel
      obtain ⟨he,hv⟩:=choice_gauge hb U t k
      have hP : (P₁).eval (Lattice.gauge k U)=(P₁).eval U :=
        Presented.lawful_gi (R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below).good k U
      rw [he,hv,hP]
      rw [show Lattice.gauge (k ∘ (Δ).ratio.embed) ((Δ).prediction U t)=(Δ).prediction U t by
        funext e; simp [Lattice.gauge,hk]]
    _ = _ := (Normal.mass_total (Δ) (β) V (P₁).eval hp hb).trans
      (congrFun (R.makes.wilson.steps d.cutoff d.period d.level d.below).1 V).symm

omit [Fintype ι] in
/-- The estimate sums the full weighted polynomial price inside each sample.
No factor for the number of modes, tags, sites or admitted aperture occurs. -/
theorem price (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (closed : ∀ t,MeasurableSet (A t)) (V : Coarse) (w : ι→ℝ) (hw : ∀ i,0<w i)
    (Y : Fine→Poly Γ) (hy : Leaf.All fun U => ((P₁).eval U:ℂ) • Y U)
    {c : ℝ} (h : ∀ U,Poly.price w (Y U)≤c) :
    Poly.price w ((((P₀).eval V:ℂ)⁻¹) • (∑ t : (Δ).Choices,column F t (A t) (β) V
      (fun U=>((P₁).eval U:ℂ) • Y U))) ≤ c := by
  let Z (U : Fine) := ((P₁).eval U:ℂ) • Y U
  have hp := Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below
  have hb := (R.family.path.levels.blocks d.level d.period).branches
  have hc := (Poly.nonnegative hw (Y 1)).trans (h 1)
  have one (t : (Δ).Choices) : Poly.price w (column F t (A t) (β) V Z) ≤
      c*(∫ a,Normal.view (Δ) (β) V t (P₁).eval (F.drape a) ∂F.order G) := by
    let f := (A t).indicator (stack t V (β) Z ∘ F.drape)
    have good := (good_slice F t V (β) hb hy).on_window (closed t)
    have paid := norm_charge (F.order G) w hw f good
    apply paid.trans
    rw [←integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ fun a=>Poly.nonnegative hw _)
      (((Normal.view_bound (Δ) (β) V t (P₁).eval hp hb).comp_env F.continuous_drape.measurable).integrable _ |>.const_mul c)
    apply ae_of_all
    intro a
    have H := Normal.view_positive (Δ) (β) V t (P₁).eval hp (F.drape a)
    by_cases ha : a∈A t
    · simp only [f,Set.indicator_of_mem ha,Function.comp_apply,stack,Z,Poly.adapted,
        Complex.norm_real,Real.norm_of_nonneg (kernel_nonneg ..),Real.norm_of_nonneg (hp.positive _).le,Normal.view]
      calc
        _ ≤ taggedKernel (Δ) (β) t (F.drape a) V*((P₁).eval (F.drape a)*c) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h _) (hp.positive _).le) (kernel_nonneg ..)
        _ = _ := by ring
    · simp only [f,Set.indicator_of_notMem ha,Poly.zero_price]
      exact mul_nonneg hc H
  have Hnorm : 0<(P₀).eval V := Multi.AxisShift.chosen_positive R.makes.wilson d.below.le V
  rw [Poly.adapted,norm_inv,Complex.norm_real,Real.norm_of_nonneg Hnorm.le,
    inv_mul_eq_div,div_le_iff₀ Hnorm]
  apply (Poly.batch hw _ _).trans
  exact (Finset.sum_le_sum (fun t _=>one t)).trans_eq
    (by rw [←Finset.mul_sum,total R d F V])

variable {J : Request ι} {U : NumericSchedule R.family J} {H : AnalyticInput J U d}
    {η : ℝ} (I : FullPreparedInputAt H η) (x : IndependentTests J.tests)
local notation "W" => fun v => H.inputRadii v/H.kernelCosts v
local notation "M" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card ι) (U.admittedCost d.level)

/-- A genuine period-independent conditional estimate for the older
ordinary marked residual. The prior vacuum is the selected positive one. -/
theorem regular (F : Forest (Δ).ratio) (A : (Δ).Choices→Set (F.Slice G))
    (closed : ∀ t,MeasurableSet (A t)) (V : Coarse) :
    Poly.price (W) (((P₀).eval V:ℂ)⁻¹ • (∑ t : (Δ).Choices,column F t (A t) (β) V
      (fun y=>((P₁).eval y:ℂ) • WilsonReceivedMarkedCofactor.regular R d I x y))) ≤
      M*(Real.exp ((Fintype.card ι:ℝ)*I.regularPrice)-1) := by
  apply price R d F A closed V _ (fun i=>div_pos (H.input_radius_positive i) (H.kernel_positive i)) _
    ?_ (fun y=>(WilsonReceivedMarkedCofactor.price R d I x y).1)
  let x₀ := testInclusion J.tests x
  have E := I.prepared.remainder_price.regular_error_envelope H.kernel_positive I.wellFormed.threshold x
  have B : Leaf.All (fun y=>Poly.pass ((I.prepared.remainder.leaf x₀).log y)-1) := by
    intro s
    obtain ⟨b,hb⟩ := E.cost
    exact ⟨(Poly.get s).continuous.measurable.comp E.meas,b,
      fun y => (norm_le_pi_norm (Poly.part _) s).trans (hb y)⟩
  have Z := Leaf.mul (ManuscriptQLocalActualLog.floor R d H x₀).safe B
  simpa only [WilsonReceivedMarkedCofactor.regular,WilsonReceivedMarkedCofactor.model,x₀,
    ManuscriptQLocalActualLog.literal,smul_mul_assoc] using Z

end YM.Integration.WilsonReceivedMarkedAperture
