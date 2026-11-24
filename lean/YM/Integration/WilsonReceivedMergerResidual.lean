import YM.Integration.WilsonReceivedEqualDensity

/-! On a fieldwise reclosed Wilson vacuum, the paid earlier regular
response splits off within each original marked numerator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedMergerResidual
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
local notation "Outer" => Config G (R.family.side d.level d.period)
variable [Fintype I] {J : Request I} {A : NumericSchedule R.family J} {H : AnalyticInput J A d}
variable {η : ℝ} (packet : FullPreparedInputAt H η) (received : Retained.NativeIntake packet)
variable (x : IndependentTests J.tests)

local notation "X" => testInclusion J.tests x
local notation "arriving" => (packet.input.leaf (X)).density
local notation "analytic" => ManuscriptQLocalActualLog.source R d H (X)
local notation "forced" => WilsonReceivedMarkedCofactor.compulsory R d packet x

variable (v : Config G (R.family.side d.level d.period))
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
variable (same : ∀ U : Config G (R.family.side (d.level+1) d.period),
  packet.carrier.rep.eval U = (R.family.path.rep d.cutoff d.period (d.level+1)).eval U)
local notation "z" => ((P₀).eval v : ℂ)
local notation "reg" => WilsonReceivedMarkedCofactor.regular R d packet x
local notation "weighted" => (fun U : Fine => ((P).eval U : ℂ) • reg U)
local notation "residual" => (arriving - analytic)
local notation "debit" => (z⁻¹ • Actual.Push Δ (P).beta (residual) v : Poly Γ)
local notation "contact" => (z⁻¹ • Actual.Push Δ (P).beta forced v : Poly Γ)
local notation "income" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card I) (A.admittedCost d.level)
local notation "toll" => fun i => H.inputRadii i/H.kernelCosts i
local notation "budget" => income * (Real.exp ((Fintype.card I:ℝ)*packet.regularPrice)-1)

private theorem regularSafe : Leaf.All (weighted) := by
  let E := packet.prepared.remainder_price.regular_error_envelope H.kernel_positive packet.wellFormed.threshold x
  have B : Leaf.All (fun u=>Poly.pass ((packet.prepared.remainder.leaf (X)).log u)-1) := by
    intro s
    obtain ⟨c,hc⟩ := E.cost
    exact ⟨(Poly.get s).continuous.measurable.comp E.meas,c,
      fun u=>(norm_le_pi_norm (Poly.part _) s).trans (hc u)⟩
  have Z := Leaf.mul (ManuscriptQLocalActualLog.floor R d H (X)).safe B
  simpa only [WilsonReceivedMarkedCofactor.regular,WilsonReceivedMarkedCofactor.model,
    ManuscriptQLocalActualLog.literal,smul_mul_assoc] using Z

include received same in
/-- The compulsory part remains a signed push on the same genuine kernel. -/
theorem original (s : Γ.Mode) :
    (debit).part s = actualAverage R.family (N:=d.cutoff) (fun U => (reg U).part s) v +
      (contact).part s := by
  have rwgt := regularSafe R d packet x
  have diff := Actual.leaf_sub (ManuscriptQLocalPrepared.input R d packet received x).1
    (ManuscriptQLocalActualLog.floor R d H (X)).safe
  have off : forced = (residual) - (weighted) := by
    funext U
    change forced U = (residual) U - (weighted) U
    rw [WilsonReceivedEqualDensity.components R d packet x same U]
    abel
  have forceSafe : Leaf.All forced := off ▸ Actual.leaf_sub diff rwgt
  have split : Actual.atMark s (residual) = Actual.atMark s (weighted) + Actual.atMark s forced :=
    funext fun U => congrArg (fun c : Poly Γ => c.part s)
      (WilsonReceivedEqualDensity.components R d packet x same U)
  have mode : Actual.atMark s (weighted) = fun U => ((P).eval U : ℂ) * (reg U).part s :=
    funext fun U => Poly.part_smul _ _ s
  have average : actualAverage R.family (N:=d.cutoff) (fun U => (reg U).part s) v =
      z⁻¹ * (Δ).push (P).beta (Actual.atMark s (weighted)) v := by
    rw [mode]
    simpa only [Complex.real_smul,Complex.ofReal_inv] using
      (actualAverage_push R.family (N:=d.cutoff) (fun U => (reg U).part s) v)
  rw [Poly.part_smul,Poly.part_smul,congrFun (Actual.grades (S:=Δ) (D:=residual) (J:=v) (β:=(P).beta)) s,
    congrFun (Actual.grades (S:=Δ) (D:=forced) (J:=v) (β:=(P).beta)) s,
    split,StepData.push_add (R.family.path.levels.transition_mass d.level d.period (P).beta) _ _
      ((rwgt s).integrableC _) ((forceSafe s).integrableC _),Pi.add_apply,mul_add,average]

include received same in
theorem paid (s : Γ.Mode) :
    ‖(debit).part s - (contact).part s‖ ≤ budget / Poly.toll toll s := by
  rw [original R d packet received x v same s,add_sub_cancel_right]
  apply actualAverage_norm_le R.family R.makes d.below
  intro U
  have hw (i) : 0<(toll) i := div_pos (H.input_radius_positive i) (H.kernel_positive i)
  apply (le_div_iff₀ (Poly.worth hw s)).2
  rw [mul_comm]
  exact (Poly.member hw s _).trans (WilsonReceivedMarkedCofactor.price R d packet x U).1

end YM.Integration.WilsonReceivedMergerResidual
