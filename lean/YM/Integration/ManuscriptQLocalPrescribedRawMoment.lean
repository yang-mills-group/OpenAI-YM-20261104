import YM.Integration.ManuscriptQLocalOriginalMaskRate
import YM.Integration.ManuscriptQLocalVariableReserve

/-! Measured physical remainder at the original engineering grades of a funded prescribed source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalPrescribedRawMoment
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot Marker OPE.Therm Comparison.RG02
open Comparison.Density.RenderM Comparison.Density.RenderM.Token ActualRunPacketRetuning
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric Pert.Asymptotics
open ManuscriptQLocalOriginalConditionalTail ManuscriptQLocalRegularConditional ManuscriptQLocalSourceFourier
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock
open Push.PriceCompiler Next.Foundations OPE.Therm
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
  (R : Run G) {J : Request V} (A : NumericSchedule R.family J)

/-- Each auxiliary value uses the same original positive transition and
true scalar density. It is a Borel function of the measured coarse field. -/
theorem values (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d) {fee : ℝ} (H : ManuscriptQLocalVariableReserve.Charged F fee) (x : IndependentTests J.tests)
    (weak : regulatorRun R.family d.cutoff d.period (d.level+1)≤1) (z : ℂ) :
    let g := regulatorRun R.family d.cutoff d.period (d.level+1)
    let p := (R.family.path.rep d.cutoff d.period (d.level+1)).p
    let P₀ := F.packets
    Measurable (fun U=>Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ p g x) z)) := by
  let g := regulatorRun R.family d.cutoff d.period (d.level+1)
  let p := (R.family.path.rep d.cutoff d.period (d.level+1)).p
  let P₀ := F.packets
  let w := fun v=>F.inputRadii v/F.kernelCosts v
  let mode := fun i:Live P₀=>P₀.mode i
  let f := field P₀ p g x
  let χ := ManuscriptQLocalPhysicalConditional.charge P₀ p.threshold g
  have hg : 0<g := IterationFour.Currency.g_pos R.makes _ _ _ d.below
  have buy := ManuscriptQLocalPhysicalConditional.reserve P₀ H p.threshold g (A.admittedCost d.level) p.threshold_pos.le hg
    (ManuscriptQLocalPhysicalConditional.threshold R d A) (A.admitted_cost_ge_one _)
  have hχ (i:Live P₀) : 0≤χ i := (ManuscriptQLocalPhysicalConditional.cold P₀ H p g x i).1
  have raw (i:Live P₀) (T) : ‖f i T‖≤χ i := (ManuscriptQLocalPhysicalConditional.cold P₀ H p g x i).2 T
  have up : 1≤g⁻¹ := (one_le_inv₀ hg).2 weak
  have hz := ManuscriptQLocalCountableConditional.whole mode (slot P₀) f H.positive hχ raw up buy z
  have q := ManuscriptQLocalCountableConditional.quiet mode (slot P₀) f H.positive hχ raw up buy (hot P₀) z
  have ms := ManuscriptQLocalCountableConditional.measured mode (slot P₀) f
    (fun i=>masked_measurable _ _ _ (ManuscriptQLocalOriginalFineMaskLoss.row_borel P₀ x i)) z
  exact ManuscriptQLocalMeasuredMarkTransport.measured_log R.family R.makes d.below (source P₀ p g x z)
    (ManuscriptQLocalMeasuredMarkTransport.env H.positive R.family (source P₀ p g x z) ms (fun T=>(hz T).2)) q

private theorem add_power {u v : ℝ} (hu : 0≤u) (hv : 0≤v) (j : ℕ) :
    (u+v)^j≤(2:ℝ)^j*(u^j+v^j) := by
  by_cases h : u≤v
  · calc _ ≤ (2*v)^j := pow_le_pow_left₀ (add_nonneg hu hv) (by linarith only [h]) j
         _ = _ := mul_pow _ _ _
         _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg hu _)) (by positivity)
  · calc _ ≤ (2*u)^j := pow_le_pow_left₀ (add_nonneg hu hv) (by linarith only [le_of_not_ge h]) j
         _ = _ := mul_pow _ _ _
         _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hv _)) (by positivity)

/-- Every polynomial coefficient uses the original powers and ranks before the source is integrated against the physical conditional. -/
theorem measured_on (fee:ℕ→ℝ) (nonnegative:∀m,0≤fee m) (flat:ActualRunSubpowerShift.Subpower R fee) (hG : G.Simple) (W : Poetry R.family.path.levels) (k j : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m:ℕ in atTop,∀d:LocalFormal.Datum R.family Γ,d.level=m→∀(F:AnalyticInput J A d),ManuscriptQLocalVariableReserve.Charged F (fee d.level)→∀
    (x : IndependentTests J.tests) (s : Γ.Mode),
    let g := regulatorRun R.family d.cutoff d.period (d.level+1)
    let B := (R.family.path.rep d.cutoff d.period (d.level+1)).p
    let w := fun v=>F.inputRadii v/F.kernelCosts v
    let P₀ := F.packets
    let D := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
    let L z U := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ B g x) z)
    let raw := ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) (F.packets.read (testInclusion J.tests x) g)
    let μ := scene R.family.path d.cutoff d.period d.level
    let C := ManuscriptQLocalRegularCalendar.constant (J:=J) Γ
    let rate := g^((k+1:ℕ)-δ:ℝ)
    ∃q:Config G (R.family.side d.level d.period)→Polynomial ℂ,
      (∀U,(q U).natDegree≤D) ∧ (∀U z,(q U).eval z=(L z U).part s) ∧
      Measurable (fun U=>ManuscriptQLocalConditionalGradeTail.low (q U) D k) ∧
      Integrable (fun U=>(Poly.toll w s*‖(raw U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖)^(j+1)) μ ∧
      ∫U,(Poly.toll w s*‖(raw U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖)^(j+1) ∂μ ≤
        ((2:ℝ)^(j+1)*(1+C^(j+1)))*rate^(j+1) := by
  filter_upwards [ManuscriptQLocalVariableReserve.original Γ R A hG fee nonnegative flat k hδ,
    ManuscriptQLocalRawMaskFlat.physical (Γ:=Γ) R hG W A j ((k+1)*(j+1)) zero_lt_one,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes 1 zero_lt_one)]
    with m saved thermal little d hd F H x s
  subst m
  let g := regulatorRun R.family d.cutoff d.period (d.level+1)
  let B := (R.family.path.rep d.cutoff d.period (d.level+1)).p
  let w := fun v=>F.inputRadii v/F.kernelCosts v
  let X := F.packets.read (testInclusion J.tests x) g
  let Y := source F.packets B g x 1
  let L := ManuscriptQLocalMeasuredMarkTransport.logarithm (Γ:=Γ) R.family (N:=d.cutoff) (m:=d.level) (p:=d.period)
  let μ := scene R.family.path d.cutoff d.period d.level
  let P₀ := F.packets
  let D := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
  let C := ManuscriptQLocalRegularCalendar.constant (J:=J) Γ
  let r := g^((k+1:ℕ)-δ:ℝ)
  let hot := fun U=>Poly.price w (L X U-L Y U)
  letI : IsProbabilityMeasure μ := probability (H:=R.family.path) (p:=d.period) R.makes.wilson d.below.le
  have hg : 0<g := IterationFour.Currency.g_pos R.makes _ _ _ d.below
  have weak : g≤1 := (little d.cutoff d.period d.below).le
  choose q deg eval price using (fun U=>saved d rfl F H x U s)
  have low_borel := ManuscriptQLocalRawSourceGrade.projection q _ (fun z=>(Poly.get s).continuous.measurable.comp (values R A d F H x weak z)) deg eval k
  refine ⟨q,deg,eval,low_borel,?_⟩
  have zero (U) : 0≤hot U := Poly.nonnegative F.input_paid.positive _
  have hr : 0≤r := Real.rpow_nonneg hg.le _
  have hc : 0≤C := by
    have q₀ : 0≤connectedBill Γ (Fintype.card V) := ManuscriptQLocalRegularCalendar.log_pos _
      (mul_nonneg (Nat.cast_nonneg _) (ManuscriptQLocalRegularCalendar.exp_pos _ (Nat.cast_nonneg _)))
    exact mul_nonneg (Nat.cast_nonneg _) q₀
  have Xcap T := (ManuscriptQLocalOriginalFineMaskLoss.original_rows F.packets F.input_paid x T).2
  have Ycap T := (ManuscriptQLocalOriginalFineMaskLoss.regular_rows F.packets F.input_paid x B T).2
  have Z T := ManuscriptQLocalOriginalFineMaskLoss.means_quiet F.packets F.input_paid x B T
  have moment : Integrable (fun U=>(hot U)^(j+1)) μ :=
    ManuscriptQLocalMeasuredMarkTransport.finite_moment F.input_paid.positive R.family R.makes d.below X Y
      (ManuscriptQLocalOriginalFineMaskLoss.full_borel F.packets x) (ManuscriptQLocalOriginalFineMaskLoss.mask_borel F.packets x B)
      Xcap Ycap (fun T=>(Z T).1) (fun T=>(Z T).2) (j+1)
  have hb : ∫U,(hot U)^(j+1) ∂μ ≤ r^(j+1) := by
    have h := thermal d rfl F x
    have p0 : g^(k+1)≤r := by
      rw [←Real.rpow_natCast g (k+1)]
      exact Real.rpow_le_rpow_of_exponent_ge hg weak (by linarith only [hδ])
    apply (by simpa only [one_mul] using h : ∫U,(hot U)^(j+1) ∂μ≤g^((k+1)*(j+1))).trans
    rw [pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hg.le _) p0 _
  have daily U : Poly.toll w s*‖(L X U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖ ≤ hot U+C*r := by
    have part := Poly.member F.input_paid.positive s (L X U-L Y U)
    have triangle : ‖(L X U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖ ≤
        ‖(L X U).part s-(L Y U).part s‖+‖(L Y U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖ :=
      by simpa only [dist_eq_norm] using dist_triangle ((L X U).part s) ((L Y U).part s) (ManuscriptQLocalConditionalGradeTail.low (q U) D k)
    have t := mul_le_mul_of_nonneg_left triangle (Poly.worth F.input_paid.positive s).le
    rw [mul_add] at t
    exact t.trans (add_le_add part (price U))
  have purchase U : (Poly.toll w s*‖(L X U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖)^(j+1) ≤ (2:ℝ)^(j+1)*((hot U)^(j+1)+(C*r)^(j+1)) :=
    (pow_le_pow_left₀ (mul_nonneg (Poly.worth F.input_paid.positive s).le (norm_nonneg _)) (daily U) _).trans
      (add_power (zero U) (mul_nonneg hc hr) (j+1))
  have source_borel := ManuscriptQLocalOriginalFineMaskLoss.full_borel F.packets x (g:=g)
  have raw_borel := ManuscriptQLocalMeasuredMarkTransport.measured_log R.family R.makes d.below X
    (ManuscriptQLocalMeasuredMarkTransport.env F.input_paid.positive R.family X source_borel Xcap) (fun T=>(Z T).1)
  have paid := (moment.add (integrable_const ((C*r)^(j+1)))).const_mul ((2:ℝ)^(j+1))
  constructor
  · refine paid.mono' ((measurable_const.mul ((((Poly.get s).continuous.measurable.comp raw_borel).sub low_borel).norm)).pow_const _).aestronglyMeasurable ?_
    apply ae_of_all
    intro U
    rw [Real.norm_of_nonneg (pow_nonneg (mul_nonneg (Poly.worth F.input_paid.positive s).le (norm_nonneg _)) _)]
    exact purchase U
  calc _ ≤ ∫U,(2:ℝ)^(j+1)*((hot U)^(j+1)+(C*r)^(j+1)) ∂μ := by
         apply integral_mono_of_nonneg (ae_of_all _ fun U=>pow_nonneg (mul_nonneg (Poly.worth F.input_paid.positive s).le (norm_nonneg _)) _) paid
         exact ae_of_all _ purchase
       _ = (2:ℝ)^(j+1)*((∫U,(hot U)^(j+1) ∂μ)+(C*r)^(j+1)) := by rw [integral_const_mul,integral_add moment (integrable_const _)];simp
       _ ≤ (2:ℝ)^(j+1)*(r^(j+1)+(C*r)^(j+1)) := mul_le_mul_of_nonneg_left (add_le_add hb le_rfl) (by positivity)
       _ = _ := by rw [mul_pow];ring

theorem measured (hG : G.Simple) (W : Poetry R.family.path.levels) (k j : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∀ᶠ m:ℕ in atTop,∀d:LocalFormal.Datum R.family Γ,d.level=m→∀(F:AnalyticInput J A d),ManuscriptQLocalOriginalSourceGrade.Bare F→∀
    (x : IndependentTests J.tests) (s : Γ.Mode),
    let g := regulatorRun R.family d.cutoff d.period (d.level+1)
    let B := (R.family.path.rep d.cutoff d.period (d.level+1)).p
    let w := fun v=>F.inputRadii v/F.kernelCosts v
    let P₀ := F.packets
    let D := ManuscriptQLocalShiftLedger.weight (fun _:V=>P₀.powerCap+P₀.rankCap) s
    let L z U := Extra.Trajectories.connected (moment R.family (N:=d.cutoff) U (source P₀ B g x) z)
    let raw := ManuscriptQLocalMeasuredMarkTransport.logarithm R.family (N:=d.cutoff) (F.packets.read (testInclusion J.tests x) g)
    let μ := scene R.family.path d.cutoff d.period d.level
    let C := ManuscriptQLocalRegularCalendar.constant (J:=J) Γ
    let rate := g^((k+1:ℕ)-δ:ℝ)
    ∃q:Config G (R.family.side d.level d.period)→Polynomial ℂ,
      (∀U,(q U).natDegree≤D) ∧ (∀U z,(q U).eval z=(L z U).part s) ∧
      Measurable (fun U=>ManuscriptQLocalConditionalGradeTail.low (q U) D k) ∧
      Integrable (fun U=>(Poly.toll w s*‖(raw U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖)^(j+1)) μ ∧
      ∫U,(Poly.toll w s*‖(raw U).part s-ManuscriptQLocalConditionalGradeTail.low (q U) D k‖)^(j+1) ∂μ ≤
        ((2:ℝ)^(j+1)*(1+C^(j+1)))*rate^(j+1) :=
  measured_on R A A.admittedCost A.admitted_cost_nonnegative (FullQLocal.PreRun.CostProfile.scalar_subpower_of_schedule R A) hG W k j hδ

end YM.Integration.ManuscriptQLocalPrescribedRawMoment
end
