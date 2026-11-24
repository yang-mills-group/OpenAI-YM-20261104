import YM.Integration.WilsonReceivedIndependentRemainder
import YM.Integration.ActualPolynomialContraction

/-! Price of the complete ordinary marked part of the inherited error under
the original Wilson history, with its analytic companion on the same field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedRegularTransport
open Function Filter MeasureTheory Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree
open Matrix Pressure Pressure.Testing Pressure.Stores Next.SectorChange Next.SectorChange.Rows
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open scoped Topology BigOperators Classical
variable {G:Gauge}{I:Type} [DecidableEq I] {Γ:Census I}(R:Run G)(d:LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "K" => d.kernel (RunFormalChain.fromRun R)
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "Coarse" => fieldDir G (R.family.side d.level d.period) 1
variable (allocation : Allocation G (R.family.path.levels.clock.op d.level d.period) (R.alloy.B.a.clock.hatBeta d.level)
  (R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) (q : Chi)
local notation "Outer" => Config G (R.family.side d.level d.period)
variable [Fintype I] {J : Request I} {A : NumericSchedule R.family J} {H : AnalyticInput J A d}
variable {η : ℝ} (packet : FullPreparedInputAt H η) (received : Retained.NativeIntake packet)
variable (rep : packet.carrier.rep = R.family.path.rep d.cutoff d.period (d.level+1)) (x : IndependentTests J.tests)

local notation "X" => testInclusion J.tests x
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
local notation "reg" => WilsonReceivedMarkedCofactor.regular R d packet x
local notation "weighted" => fun U : Fine => (((P).eval U : ℂ) • reg U : Poly Γ)
local notation "forced" => WilsonReceivedMarkedCofactor.compulsory R d packet x
local notation "cash" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card I) (A.admittedCost d.level)
local notation "fee" => fun i => H.inputRadii i/H.kernelCosts i
local notation "bound" => cash * (Real.exp ((Fintype.card I:ℝ)*packet.regularPrice)-1)

private theorem safe : Leaf.All (weighted) := by
  let E := packet.prepared.remainder_price.regular_error_envelope H.kernel_positive packet.wellFormed.threshold x
  have B : Leaf.All (fun u=>Poly.pass ((packet.prepared.remainder.leaf (X)).log u)-1) := by
    intro s
    obtain ⟨c,hc⟩ := E.cost
    exact ⟨(Poly.get s).continuous.measurable.comp E.meas,c,
      fun u=>(norm_le_pi_norm (Poly.part _) s).trans (hc u)⟩
  have Z := Leaf.mul (ManuscriptQLocalActualLog.floor R d H (X)).safe B
  simpa only [WilsonReceivedMarkedCofactor.regular,WilsonReceivedMarkedCofactor.model,
    ManuscriptQLocalActualLog.literal,smul_mul_assoc] using Z

private theorem measurable_reg : Measurable reg := by
  have ht := Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below
  have hs := safe R d packet x
  change @Measurable _ (Γ.Mode → ℂ) _ (borel _) _
  rw [← BorelSpace.measurable_eq]
  apply measurable_pi_lambda
  intro s
  change Measurable (fun U : Fine => (reg U).part s)
  have eq : (fun U : Fine => (reg U).part s) = fun U => ((P).eval U : ℂ)⁻¹ * ((weighted) U).part s := by
    funext U
    rw [Poly.part_smul,←mul_assoc,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (ht.positive U).ne'),one_mul]
  rw [eq]
  exact (Complex.continuous_ofReal.measurable.comp ht.safe.meas).inv.mul (hs s).meas

/-- All earlier dates use their own complete positive conditional law. -/
theorem earlier {m : ℕ} (hm : m ≤ d.level+1) (v : Config G (R.family.side m d.period)) :
    Poly.price fee (actualTransport R.family (N:=d.cutoff) reg hm v) ≤ bound := by
  exact ActualPolynomialContraction.transport_price_le R.family R.makes
    (fun i=>div_pos (H.input_radius_positive i) (H.kernel_positive i)) d.below
    (measurable_reg R d packet x).aestronglyMeasurable
    (fun U=>(WilsonReceivedMarkedCofactor.price R d packet x U).1) hm v

theorem one (v : Outer) : Poly.price fee (actualAverage R.family (N:=d.cutoff) reg v) ≤ bound := by
  exact ActualPolynomialContraction.average_price_le R.family R.makes
    (fun i=>div_pos (H.input_radius_positive i) (H.kernel_positive i)) d.below
    (measurable_reg R d packet x).aestronglyMeasurable
    (fun U=>(WilsonReceivedMarkedCofactor.price R d packet x U).1) v


local notation "delta" => WilsonReceivedIndependentRemainder.cofactor R d packet x
local notation "arriving" => (packet.input.leaf (X)).density
local notation "analytic" => ManuscriptQLocalActualLog.source R d H (X)

include received in
private theorem residual : Leaf.All delta ∧ GaugeInvariant delta := by
  have actual := ManuscriptQLocalPrepared.input R d packet received x
  have ideal := ManuscriptQLocalActualLog.floor R d H (X)
  have eq : delta = arriving - analytic :=
    funext fun U => (ManuscriptQLocalActualLog.inherited R d H (X) packet U).symm
  rw [eq]
  exact ⟨Actual.leaf_sub actual.1 ideal.safe,
    fun κ U => congrArg₂ (·-·) (actual.2 κ U) (ideal.gauges κ U)⟩

private theorem component (s : Γ.Mode) (v : Outer) :
    (actualAverage R.family (N:=d.cutoff) reg v).part s =
      ((P₀).eval v : ℂ)⁻¹ * (Δ).push (P).beta (Actual.atMark s (weighted)) v := by
  let l := (Poly.get s).restrictScalars ℝ
  have hw (i) : 0<(fee) i := div_pos (H.input_radius_positive i) (H.kernel_positive i)
  obtain ⟨r,hr,norm⟩ := Poly.equivalent_norm (R:=Γ) hw
  have hn (U) : ‖reg U‖ ≤ (bound)*r := (norm _).trans
    (mul_le_mul_of_nonneg_right (WilsonReceivedMarkedCofactor.price R d packet x U).1 hr)
  have hi := actualAverage_integrable R.family R.makes d.below
    (measurable_reg R d packet x).aestronglyMeasurable hn v
  have project : (actualAverage R.family (N:=d.cutoff) reg v).part s =
      actualAverage R.family (N:=d.cutoff) (fun U => (reg U).part s) v := by
    change l (actualAverage R.family (N:=d.cutoff) reg v) = _
    unfold actualAverage
    rw [← l.integral_comp_comm hi]
    exact integral_congr_ae (ae_of_all _ (fun U => l.map_smul _ _))
  have mode : Actual.atMark s (weighted) = fun U => ((P).eval U : ℂ) * (reg U).part s :=
    funext fun U => Poly.part_smul _ _ s
  rw [mode,project]
  simpa only [Complex.real_smul,Complex.ofReal_inv] using
    (actualAverage_push R.family (N:=d.cutoff) (fun U => (reg U).part s) v)

include received rep in
theorem split (v : Outer) (angle : Coarse) :
    (((P₀).eval v : ℂ)⁻¹ •
      WilsonReceivedIndependentRemainder.correction R d allocation q packet x v angle : Poly Γ) =
      actualAverage R.family (N:=d.cutoff) reg v +
        (((P₀).eval v : ℂ)⁻¹ • Actual.Push Δ (P).beta forced v : Poly Γ) := by
  have good := residual R d packet received x
  have rwgt := safe R d packet x
  have minus : forced = delta - (weighted) := by
    funext U
    change forced U = delta U - (weighted) U
    rw [WilsonReceivedIndependentRemainder.selected R d packet rep x U]
    abel
  have rf : Leaf.All forced := minus ▸ Actual.leaf_sub good.1 rwgt
  have kernel := R.family.path.levels.transition_mass d.level d.period (P).beta
  funext s
  have reading : (WilsonReceivedIndependentRemainder.correction R d allocation q packet x v angle).part s =
      (Δ).push (P).beta (Actual.atMark s delta) v :=
    WilsonRootedNonflatLog.measured R d allocation q v angle _ (good.1 s)
      (fun κ U=>congrArg (fun z : Poly Γ => z.part s) (good.2 κ U))
  have join : Actual.atMark s delta = Actual.atMark s (weighted) + Actual.atMark s forced :=
    funext fun U => congrArg (fun z : Poly Γ => z.part s)
      (WilsonReceivedIndependentRemainder.selected R d packet rep x U)
  change ((P₀).eval v : ℂ)⁻¹ * (WilsonReceivedIndependentRemainder.correction R d allocation q packet x v angle).part s =
    (actualAverage R.family (N:=d.cutoff) reg v).part s + ((P₀).eval v : ℂ)⁻¹ * (Actual.Push Δ (P).beta forced v).part s
  rw [reading,join,StepData.push_add kernel _ _
    ((rwgt s).integrableC _) ((rf s).integrableC _),Pi.add_apply,mul_add,component R d packet x s v,
    congrFun (Actual.grades (S:=Δ) (β:=(P).beta) (J:=v) (D:=forced)) s]

include allocation q received rep in
theorem connected (angle : Coarse) :
    let v := Integral.sample g angle
    Local.cumulant P arriving Δ v = Extra.Trajectories.connected
      (WilsonReceivedIndependentRemainder.model R d (H:=H) x angle + actualAverage R.family (N:=d.cutoff) reg v +
        (((P₀).eval v : ℂ)⁻¹ • Actual.Push Δ (P).beta forced v : Poly Γ)) := by
  intro v
  rw [WilsonReceivedIndependentRemainder.connected R d allocation q packet received rep x angle,
    split R d allocation q packet received rep x v angle,add_assoc]

end YM.Integration.WilsonReceivedRegularTransport
