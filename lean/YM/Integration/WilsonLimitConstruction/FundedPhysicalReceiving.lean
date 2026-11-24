import YM.Integration.WilsonLimitConstruction.FundedCanonicalReceiving
import YM.Integration.WilsonLimitConstruction.FundedPhysicalCatalogue

/-! The genuine paid cover model issues the succeeding analytic input at
the actual next Wilson coupling, including the complete positive fine action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedPhysicalReceiving
open Filter Lattice Wilson RG Marker MeasureTheory PhysicalNext.Repeat.Legato Comparison.RG02
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun.SuccessiveRequests
open scoped Topology Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] {Γ : Census V} {J : Request V}
private def enlargeGraded {a : Side} {L : List (Piece G a)}
    {p : BudgetPoint} {order rankCap nextCap : ℕ} {width budget nextBudget : ℝ}
    (H : GradedVacuumLayers L p order rankCap width budget)
    (hc : rankCap ≤ nextCap) (hb : budget ≤ nextBudget) :
    GradedVacuumLayers L p order nextCap width nextBudget where
  packets := { H.packets with
    rank_bounded := fun a ha => (H.packets.rank_bounded a ha).trans hc
    total := H.packets.total.trans hb
    cover_cost := H.packets.cover_cost.trans hb }
  orders := H.orders
  leading_rank := H.leading_rank

private theorem enlargePaid {a : Side} {P : MarkedPackets J.tests G a Γ}
    {p : BudgetPoint} {address : V → Support a}
    {region : Comparison.Density.Testing.Region (fun v => (J.tests v).Mood) a}
    {w : V → ℝ} {g width budget nextBudget : ℝ} {offset slope : ℕ}
    (H : P.Paid p address region w g width budget offset slope)
    (hb : budget ≤ nextBudget) :
    P.Paid p address region w g width nextBudget offset slope :=
  { H with roots := fun v =>
      ⟨(H.roots v).1, (H.roots v).2.1, (H.roots v).2.2.trans hb⟩ }

variable [Fintype V]

private def fineAction {C : Family G} {D : LocalFormal.Datum C Γ}
    {W : TestSpace J.tests → Bulk.Colors Γ G (C.side (D.level + 1) D.period)}
    {L : List (Piece G (C.side (D.level + 1) D.period))}
    (H : FineWholeAction J D W L) (caps : Handoff.OutputCapacities) (r : ℕ) :
    FineWholeAction (nextRequest J caps r) D W L where
  standard := H.standard
  input_summable := H.input_summable
  inputExtension := H.inputExtension
  formalInputExtension := H.formalInputExtension
  input_extension_value := H.input_extension_value
  formal_input_extension_value := H.formal_input_extension_value
  input_extension_smooth := H.input_extension_smooth
  formal_input_extension_smooth := H.formal_input_extension_smooth
  input_whole := H.input_whole


variable (R : Run G) {d : LocalFormal.Datum R.family Γ}
    {A : NumericSchedule R.family J} {K : NumericPrices A} {F : AnalyticInput J A d}
    {η : ℝ} {I : FullPreparedInputAt F η} {caps : Handoff.OutputCapacities}
    (M : FundedPhysicalCatalogue.Purchase caps K F)
    (S : FundedRenderedBank.Chosen K I M.toCatalogue)

theorem read (P : FundedRenderedBank.Canonical S) (r : ℕ) :
    ∀ y U, (ActualRunInterpolatedPackets.onRun R d.cutoff d.period d.level
      S.bank.output.model r).read y
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level) U =
      P.bank.output.model.read y
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)) U := by
  intro y U
  have h := M.paid
  calc
    _ = S.bank.output.model.read y
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)) U :=
      ActualRunInterpolatedPackets.onRun_read R d.cutoff d.period d.level d.below
        S.bank.output.model r (by simpa only [S.bank.same_model] using h) y U
    _ = _ := by rw [S.bank.same_model,P.bank.same_model]

/-- All independent inputs and the original arbitrary next background occur
after the selected actual width, calibrated ratio, and native finite-copy bill. -/
theorem attachedWithOutput (r : ℕ) {m : ℕ} (hm : d.level = m+1)
    (A' : NumericSchedule R.family (nextRequest J caps r))
    (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
    (x : Exterior.fieldDir G (R.family.side m d.period) 1)
    (width : ℕ → ℝ) (H : FundedPhysicalCatalogue.Width width M)
    (hnorm : A'.inputNorm m = A.outputNorm d.level)
    (hwidth : width d.level = A'.inputWidth m)
    (hcost : (4:ℝ)^J.order*K.geometry d.level ≤ A'.admittedCost m)
    (lo : (1/4:ℝ) ≤ FundedCanonicalReceiving.ratio R M.toCatalogue)
    (hi : FundedCanonicalReceiving.ratio R M.toCatalogue ≤ 4)
    (packetPrice : (ActualRunInterpolatedPackets.onRun R d.cutoff d.period d.level
          S.bank.output.model r).Paid (A.outputNorm d.level) F.outputAddresses M.region
        (fun v => F.outputRadii v/F.kernelCosts v)
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level)
        (width d.level) (K.geometry d.level*2) M.coverOffset M.coverSlope)
    (eligible : ActualNextAnalyticInput.Eligibility R.family J m) :
    ∃ F' : AnalyticInput (nextRequest J caps r) A' (ActualNextLocalDatum.descend d hm W x),
      FundedCanonicalReceiving.Attached R S r hm F' ∧ F'.outputRadii = (fun v=>F.outputRadii v / A'.radiusLoss m) := by
  rcases d with ⟨N,t,level,below,forest,tag,background,field⟩
  dsimp only at hm
  subst level
  let d' := ActualNextLocalDatum.descend
    (⟨N,t,m+1,below,forest,tag,background,field⟩ : LocalFormal.Datum R.family Γ) rfl W x
  let L := FundedCanonicalReceiving.layers R M.toCatalogue
  let packets := ActualRunInterpolatedPackets.onRun R N t (m+1) S.bank.output.model r
  let vac := ActualGradedVacuum.restored L
  let colors := ActualRunInterpolatedInput.colors R N t (m+1) S.bank.output.model
    r (caps.packetPower+1) vac
  have caps' := nextRequest_caps J caps r
  have htwo : (2 : ℝ) ≤ (4:ℝ)^J.order :=
    (by norm_num : (2:ℝ) ≤ (4:ℝ)^2).trans
      (pow_le_pow_right₀ (by norm_num) J.order_ge_two)
  have packetCost : K.geometry (m+1)*2 ≤ A'.admittedCost m := by
    rw [mul_comm]
    exact (mul_le_mul_of_nonneg_right htwo (K.geometry_nonnegative (m+1))).trans hcost
  have geometry : K.geometry (m+1) ≤ A'.admittedCost m :=
    (le_mul_of_one_le_left (K.geometry_nonnegative (m+1))
      ((by norm_num : (1:ℝ) ≤ 2).trans htwo)).trans hcost
  have hpositive : 0 < width (m+1) := by
    rw [hwidth]
    exact A'.input_width_pos m
  have hg := ActualRetunedVacuumUniformCost.graded H.vacuum J.order_ge_two lo hi
  have grade : GradedVacuumLayers L (A'.inputNorm m) J.order
      (nextRequest J caps r).vacuumRankCap (A'.inputWidth m) (A'.admittedCost m) := by
    rw [hnorm,←hwidth]
    exact enlargeGraded hg caps'.1 hcost
  have hcap : S.bank.output.model.powerCap ≤ caps.packetPower := by
    rw [S.bank.same_model]
    exact M.power_bounded
  have hpowers : ∀ i T, S.bank.output.model.packet i = some T →
      0 < ((caps.packetPower+1 : ℕ):ℤ)+S.bank.output.model.power i := by
    intro i T hit
    have hp := (S.bank.output.model.power_bounded i T hit).trans hcap
    have ha : |S.bank.output.model.power i| ≤ (caps.packetPower:ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hp
    have := (abs_le.mp ha).1
    omega
  have hpStored := H.paid
  have co : InputColors colors packets :=
    ActualRunInterpolatedInput.input_colors R N t (m+1) below S.bank.output.model
      r (caps.packetPower+1) hpowers (by simpa only [S.bank.same_model] using hpStored)
      vac ((ActualGradedVacuum.restored_grade hg hpositive).lower (by decide))
      (ActualGradedVacuum.restored_gauge hg) (ActualGradedVacuum.restored_envelope hg hpositive)
  obtain ⟨fine⟩ := ActualLayerFineAction.whole_action R Γ J d' hg hpositive colors
    packets co (fun _ => rfl)
  let F' : AnalyticInput (nextRequest J caps r) A' d' := {
    whole_tests := F.whole_tests
    layers := L
    layers_paid := by
      change Render.permits L (A'.inputNorm m)
      rw [hnorm]
      exact NativeVacuumLayerRescaling.permits M.output_layers_paid _
    vacuum := grade
    fineRoots := F.coarseRoots
    coarseRoots := ActualNextLocalDatum.coarseRoots F rfl
    roots := ActualNextLocalDatum.roots F rfl
    colors := colors
    packets := packets
    convention := co
    rank_bounded := by
      change S.bank.output.model.rankCap ≤ _
      rw [S.bank.same_model]
      exact M.rank_bounded.trans caps'.2.1
    power_bounded := by
      change max S.bank.output.model.powerCap (r+2) ≤ _
      exact max_le (hcap.trans caps'.2.2.1) caps'.2.2.2
    whole_input := fineAction fine caps r
    inputRadii := F.outputRadii
    outputRadii := fun v => F.outputRadii v/A'.radiusLoss m
    kernelCosts := F.kernelCosts
    input_radius_positive := F.output_radius_positive
    output_radius_positive := fun v =>
      div_pos (F.output_radius_positive v) (A'.radius_loss_positive m)
    kernel_positive := F.kernel_positive
    radius_admission := fun v =>
      le_of_eq (div_mul_cancel₀ (F.outputRadii v) (A'.radius_loss_positive m).ne')
    inputAddresses := F.outputAddresses
    input_origins := ActualNextLocalDatum.output_roots_mem F
    inputRegion := M.region
    coverOffset := M.coverOffset
    coverSlope := M.coverSlope
    cover_cost := by
      change Real.exp ((A'.inputNorm m).supportExponent*(M.coverOffset:ℝ)) ≤ A'.admittedCost m
      rw [hnorm]
      exact M.cover_cost.trans geometry
    input_paid := by
      change packets.Paid (A'.inputNorm m) F.outputAddresses M.region _
        (Pert.Asymptotics.regulatorRun R.family N t (m+1)) (A'.inputWidth m)
        (A'.admittedCost m) M.coverOffset M.coverSlope
      rw [hnorm,←hwidth]
      exact enlargePaid packetPrice packetCost
    physical_period := F.physical_period
    input_field_admitted := eligible.input_field
    input_distance_admitted := eligible.input_distance
    output_field_admitted := eligible.output_field
    output_distance_admitted := eligible.output_distance
    primary_admitted := eligible.primary }
  exact ⟨F',⟨HEq.rfl,HEq.rfl,rfl,rfl,HEq.rfl,HEq.rfl⟩,rfl⟩

theorem attached (r : ℕ) {m : ℕ} (hm : d.level = m+1)
    (A' : NumericSchedule R.family (nextRequest J caps r))
    (W : Bulk.Colors Γ G (R.family.side (m+1) d.period))
    (x : Exterior.fieldDir G (R.family.side m d.period) 1)
    (width : ℕ → ℝ) (H : FundedPhysicalCatalogue.Width width M)
    (hnorm : A'.inputNorm m = A.outputNorm d.level)
    (hwidth : width d.level = A'.inputWidth m)
    (hcost : (4:ℝ)^J.order*K.geometry d.level ≤ A'.admittedCost m)
    (lo : (1/4:ℝ) ≤ FundedCanonicalReceiving.ratio R M.toCatalogue)
    (hi : FundedCanonicalReceiving.ratio R M.toCatalogue ≤ 4)
    (packetPrice : (ActualRunInterpolatedPackets.onRun R d.cutoff d.period d.level
          S.bank.output.model r).Paid (A.outputNorm d.level) F.outputAddresses M.region
        (fun v => F.outputRadii v/F.kernelCosts v)
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level)
        (width d.level) (K.geometry d.level*2) M.coverOffset M.coverSlope)
    (eligible : ActualNextAnalyticInput.Eligibility R.family J m) :
    ∃ F' : AnalyticInput (nextRequest J caps r) A' (ActualNextLocalDatum.descend d hm W x),
      FundedCanonicalReceiving.Attached R S r hm F' := by
  obtain ⟨F',shared,_⟩ := attachedWithOutput R M S r hm A' W x width H hnorm hwidth hcost lo hi packetPrice eligible
  exact ⟨F',shared⟩

end YM.Integration.WilsonLimitConstruction.FundedPhysicalReceiving
end
