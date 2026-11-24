import YM.Integration.WilsonReceivedMergerResidual
import YM.Integration.WilsonCoherentMayerPriorReclosure

/-! An equal-density physical reclosure on the independently filed finite Wilson material,
with signed winding and compulsory marked returns on their original normalized measures. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerWindingDensity
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
variable (angle : fieldDir G (R.family.side d.level d.period) 1)
local notation "v" => Integral.sample g angle
local notation "model" => WilsonReceivedIndependentRemainder.model R d (H:=H) x angle
local notation "z" => ((P₀).eval v : ℂ)
local notation "chosen" => ({d with colors:=H.colors (X),field:=angle} : LocalFormal.Datum R.family Γ)
local notation "finite" => Order.value (g : ℂ) ((chosen).markedLog (RunFormalChain.fromRun R) J.order)
local notation "zones" => fun _ : (Δ).Choices => Integral.zone K (P).p d.forest g angle
local notation "localError" => Local.markingError P analytic K g d.forest d.tag (H.colors (X))
  (zones) angle J.order (Fintype.card I)


local notation "material" => PhysicalWilsonPeriodizedMaterial.reference R d.cutoff d.level d.period
  d.below angle (H.colors (X)) J.order

local notation "actual" => (z⁻¹ • Actual.Push Δ (P).beta arriving v : Poly Γ)
local notation "residual" => (arriving - analytic)
local notation "debit" => (z⁻¹ • Actual.Push Δ (P).beta (residual) v : Poly Γ)
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
variable (same : ∀ U : Config G (R.family.side (d.level+1) d.period),
  packet.carrier.rep.eval U = (R.family.path.rep d.cutoff d.period (d.level+1)).eval U)


local notation "income" => MarkedPackets.uniformModelCost J.inputPacketRankCap (Fintype.card I) (A.admittedCost d.level)
local notation "toll" => fun i => H.inputRadii i/H.kernelCosts i
local notation "budget" => income * (Real.exp ((Fintype.card I:ℝ)*packet.regularPrice)-1)
local notation "contact" => (z⁻¹ • Actual.Push Δ (P).beta forced v : Poly Γ)
local notation "purse" => fun s:Γ.Mode=> budget/Poly.toll toll s + ‖(contact).part s‖
local notation "localLoss" => ∑s:Γ.Mode,Poly.toll toll s*
  (OriginalMarkedRunAction.partitionTariff model purse s+‖(localError).part s‖)
local notation "L" => Local.cumulant P arriving Δ v
local notation "printed" => Order.value (g : ℂ) (Order.logMarked material)

omit [Fintype I] in
private theorem upper (modes:Poly Γ)(δ ε:Γ.Mode→ℝ)(nonneg:∀s,0≤δ s)(bound:∀s,δ s≤ε s)(s:Γ.Mode):
    OriginalMarkedRunAction.partitionTariff modes δ s ≤ OriginalMarkedRunAction.partitionTariff modes ε s:=by
  unfold OriginalMarkedRunAction.partitionTariff
  refine Finset.sum_le_sum fun t _=>mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine sub_le_sub_right ?_ _
  exact Finset.prod_le_prod (fun j _=>add_nonneg (norm_nonneg _) (nonneg _))
    (fun j _=>add_le_add le_rfl (bound j.val))

include received same in
theorem measured (s:Γ.Mode):
    ‖(L).part s-(printed).part s‖ ≤ OriginalMarkedRunAction.partitionTariff model purse s+
      ‖(localError).part s‖:=by
  have amount (j:Γ.Mode):‖(debit).part j‖≤(purse) j:=by
    calc
      _ = ‖((debit).part j-(contact).part j)+(contact).part j‖:=by rw [sub_add_cancel]
      _ ≤ _ := (norm_add_le ..).trans (add_le_add
        (WilsonReceivedMergerResidual.paid R d packet received x v same j) le_rfl)
  exact (WilsonReceivedEqualDensity.measured R d packet received x angle same s).trans
    (add_le_add (upper model (fun j=>‖(debit).part j‖) purse (fun _=>norm_nonneg _) amount s) le_rfl)

include received same in
/-- A signed full-mode winding bound on this material can be spent without equating two
hard books. The same arbitrary earlier marked multiplier appears on the physical outcome. -/
theorem reclosed (Y Z:Poly Γ)(proper:Y.part Γ.quiet=0) {ω:ℝ}
    (winding:Poly.price toll (Y-(printed))≤ω):
    (actual).part Γ.quiet=1 ∧
    Poly.pass Y*Z=Poly.pass (Y-(L))*((actual)*Z) ∧
    Poly.price toll (Poly.pass Y*Z-(actual)*Z)≤
       (Real.exp (localLoss+ω)-1)*Poly.price toll ((actual)*Z):=by
  have hw (i):0<(toll) i:=div_pos (H.input_radius_positive i) (H.kernel_positive i)
  obtain ⟨one,law⟩:=WilsonReceivedEqualDensity.normalized R d packet received x angle same
  have quiet:(L).part Γ.quiet=0:=law ▸ Extra.Trajectories.connected_quiet one
  have arrived:(actual)*Z=Poly.pass (L)*Z:=by rw [law,Extra.Trajectories.pass_connected one]
  obtain ⟨replaced,fee⟩:=WilsonCoherentMayerPriorReclosure.price hw (L) Y Z ((actual)*Z) quiet proper arrived
  have native:Poly.price toll ((printed)-(L))≤localLoss:=by
    unfold Poly.price
    refine Finset.sum_le_sum fun s _=>mul_le_mul_of_nonneg_left ?_ (Poly.worth hw s).le
    change ‖(printed).part s-(L).part s‖≤_
    rw [norm_sub_rev]
    exact measured R d packet received x angle same s
  have both:Poly.price toll (Y-(L))≤localLoss+ω:=by
    rw [show Y-(L) = ((printed)-(L))+(Y-(printed)) from by abel]
    exact (Poly.addition hw ..).trans (add_le_add native winding)
  exact ⟨one,replaced,fee.trans (mul_le_mul_of_nonneg_right
    (sub_le_sub_right (Real.exp_le_exp.mpr both) _) (Poly.nonnegative hw _))⟩

end YM.Integration.WilsonCoherentMayerWindingDensity
