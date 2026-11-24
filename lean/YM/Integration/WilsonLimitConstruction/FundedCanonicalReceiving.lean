import YM.Integration.WilsonLimitConstruction.FundedCanonicalInputPayload
import YM.Integration.ActualNextPreparedInput

/-! The physically reclosed signed bank feeds its entire charged functional
and its paid nonlinear remainder into the following original RG step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedCanonicalReceiving
open Filter Lattice Wilson RG Marker MeasureTheory
open PhysicalNext.Repeat.Legato Comparison.RG02
open IterationFour IterationFour.Vacuum
open RG3.Script.Picnic LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open FullQLocal.PreRun.SuccessiveRequests
open scoped Classical BigOperators

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {J : Request V} (R : Run G) {d : LocalFormal.Datum R.family Γ}

def ratio (M : FundedRenderedBank.Catalogue J d) : ℝ :=
  Currency.gain (M.plan.predict d.level) / Currency.g R.family d.cutoff d.period d.level

def layers (M : FundedRenderedBank.Catalogue J d) :
    List (Piece G (R.family.side d.level d.period)) :=
  NativeVacuumLayerRescaling.layers (ratio R M) (M.plan.layers d.level)

omit [Fintype V] in
theorem rendered (M : FundedRenderedBank.Catalogue J d) (p : BudgetPoint) (U) :
    Render.renders (Render.prefactor (Currency.g R.family d.cutoff d.period d.level))
      p U (layers R M) =
    Render.renders (Render.prefactor (Currency.gain (M.plan.predict d.level)))
      p U (M.plan.layers d.level) := by
  have hg : 0 < Currency.g R.family d.cutoff d.period d.level :=
    Currency.g_pos R.makes d.cutoff d.period d.level d.below.le
  have cancel : Currency.gain (M.plan.predict d.level) / Currency.g R.family d.cutoff d.period d.level *
      Currency.g R.family d.cutoff d.period d.level = Currency.gain (M.plan.predict d.level) :=
    div_mul_cancel₀ _ hg.ne'
  unfold layers ratio
  rw [NativeVacuumLayerRescaling.renders, cancel]

variable {A : NumericSchedule R.family J} {K : NumericPrices A}
    {F : AnalyticInput J A d} {η : ℝ} {I : FullPreparedInputAt F η}
    {M : FundedRenderedBank.Catalogue J d} {caps : Handoff.OutputCapacities}

/-- The six identities assert where every row, address, and price of the next
analytic input came from. The next level may choose its own forest and field. -/
structure Attached (S : FundedRenderedBank.Chosen K I M) (r : ℕ) {m : ℕ}
    (hm : d.level = m+1) {A' : NumericSchedule R.family (nextRequest J caps r)}
    {W : Bulk.Colors Γ G (R.family.side (m+1) d.period)}
    {x : Exterior.fieldDir G (R.family.side m d.period) 1}
    (F' : AnalyticInput (nextRequest J caps r) A' (ActualNextLocalDatum.descend d hm W x)) : Prop where
  roots : HEq F'.fineRoots F.coarseRoots
  addresses : HEq F'.inputAddresses F.outputAddresses
  radii : F'.inputRadii = F.outputRadii
  costs : F'.kernelCosts = F.kernelCosts
  packets : HEq F'.packets
    (ActualRunInterpolatedPackets.onRun R d.cutoff d.period d.level S.bank.output.model r)
  vacuum : HEq F'.layers (layers R M)

private theorem move {C : Family G} {D : V → ComparisonDensity.Address.Orbit}
    {N t l : ℕ} (T : PhysicalCarrier C N t l) (p : BudgetPoint)
    {roots roots' : V → Site (C.side l t)} {addr addr' : V → Support (C.side l t)}
    {ρ ρ' : V → ℝ} {κ κ' : Γ.Mode → ℝ} {ord forced : ℝ}
    {colors : TestSpace D → Bulk.Colors Γ G (C.side l t)}
    {packets : MarkedPackets D G (C.side l t) Γ}
    (z : Taste (TestSpace D) roots T.rep Γ)
    (Q : PreparedWithRemainderAt N t l p (Handoff.legacyCarrier T)
      roots z colors packets ρ κ ord forced)
    (linear : Multilinear D z) (retains : FunctionalRetains z addr)
    (hr : roots' = roots) (ha : addr' = addr) (hw : ρ' = ρ) (hk : κ' = κ) :
    ∃ (z' : Taste (TestSpace D) roots' T.rep Γ)
      (Q' : PreparedWithRemainderAt N t l p (Handoff.legacyCarrier T)
        roots' z' colors packets ρ' κ' ord forced),
      HEq z' z ∧ HEq Q'.remainder Q.remainder ∧
        Multilinear D z' ∧ FunctionalRetains z' addr' := by
  subst roots'
  subst addr'
  subst ρ'
  subst κ'
  exact ⟨z,Q,HEq.rfl,HEq.rfl,linear,retains⟩

/-- This receiver consumes the original complete functional and nonlinear
residual at the outgoing regulator and the calibrated vacuum exponent
at the incoming regulator. The same carrier pays both hard inventories. -/
theorem prepare (S : FundedRenderedBank.Chosen K I M) (P : FundedRenderedBank.Canonical S)
    (r : ℕ) {m : ℕ} (hm : d.level = m+1)
    {A' : NumericSchedule R.family (nextRequest J caps r)}
    {W : Bulk.Colors Γ G (R.family.side (m+1) d.period)}
    {x : Exterior.fieldDir G (R.family.side m d.period) 1}
    (F' : AnalyticInput (nextRequest J caps r) A' (ActualNextLocalDatum.descend d hm W x))
    (shared : Attached R S r hm F') (hnorm : A'.inputNorm m = A.outputNorm d.level)
    (hG : G.Simple)
    (hw : AnalyticBridge.VerifiedReset.Geo.Width (A.outputNorm d.level)
      (R.family.path.levels.params d.level).clip (R.family.path.levels.params d.level).width)
    (permits : Render.permits (M.plan.layers d.level) (A.outputNorm d.level))
    {η' : ℝ} (C : CalibrationPresentation P.bank.output.carrier.rep (A'.inputNorm m) η')
    (hC : ∀ U, C.amount U =
      (P.bank.output.carrier.rep.beta - R.family.path.β d.cutoff d.period d.level) *
      Push.BetaTransport.kinetic (R.family.path.rep d.cutoff d.period d.level).path
        (R.family.path.levels.params d.level).clip (A'.inputNorm m) U)
    (hInherited : FundedCanonicalInputPayload.errorPrice R I K ≤ J.inheritedConstant *
      Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level ^
        ((J.order : ℝ)+1-J.eta))
    (q : ℕ) (bounds : FundedRenderedBank.Bounds K I M P.bank 1 q)
    (hForced : Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)^q ≤
      J.forcedConstant)
    (read : ∀ y U, (ActualRunInterpolatedPackets.onRun R d.cutoff d.period d.level
          S.bank.output.model r).read y
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period d.level) U =
      P.bank.output.model.read y
        (Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)) U) :
    ∃ L : FullPreparedInputAt F' η',
      HEq L.carrier P.bank.output.carrier ∧ HEq L.input P.bank.output.output ∧
      HEq L.prepared.remainder P.bank.output.residual ∧
      L.inherited = FundedCanonicalInputPayload.errorPrice R I K ∧
      L.regularPrice = Retained.ordinaryRate K I 1 ∧
      L.forcedPrice = Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)^q ∧
      (0 ≤ η → Retained.NativeIntake I → Retained.ordinaryRate K I 1 ≤ 1 →
        Retained.NativeIntake L) := by
  rcases d with ⟨N, t, level, below, forest, tag, colors, field⟩
  dsimp only at hm
  subst level
  have invoice := FundedCanonicalInputPayload.invoice R S hG hw (A'.inputNorm m)
    (congrArg BudgetPoint.threshold hnorm) (congrArg BudgetPoint.B hnorm)
    (le_of_eq (congrArg BudgetPoint.order hnorm))
    (le_of_eq (congrArg BudgetPoint.power hnorm))
    (le_of_eq (congrArg BudgetPoint.supportExponent hnorm))
  have hPackets : F'.packets = ActualRunInterpolatedPackets.onRun R N t (m+1)
      S.bank.output.model r := eq_of_heq shared.packets
  have hRead : ∀ y U, F'.packets.read y
      (Pert.Asymptotics.regulatorRun R.family N t (m+1)) U =
      P.bank.output.model.read y
        (Pert.Asymptotics.regulatorRun R.family N t (m+1+1)) U := by
    rw [hPackets]
    exact read
  have budget := bounds.residual_price
  rw [← hnorm] at budget
  let Q := prepareProduced P.bank.output (A'.inputNorm m) F'.colors F'.packets
    F.outputRadii F.kernelCosts (Retained.ordinaryRate K I 1)
    (Pert.Asymptotics.regulatorRun R.family N t (m+1+1)^q) F'.convention hRead budget
  obtain ⟨z,Q',hz,hQ,hLin,hKeep⟩ := move P.bank.output.carrier (A'.inputNorm m)
    P.bank.output.output Q P.bank.output_multilinear P.bank.output_retains
    (eq_of_heq shared.roots) (eq_of_heq shared.addresses) shared.radii
    (congrArg envelopeProduct shared.costs)
  have hWf : WellFormed (A'.inputNorm m) P.bank.output.carrier.rep := by
    rw [hnorm]
    exact P.bank.wellFormed
  let L : FullPreparedInputAt F' η' := {
    carrier := P.bank.output.carrier
    wellFormed := hWf
    inherited := FundedCanonicalInputPayload.errorPrice R I K
    inherited_nonnegative := IterationFour.Vacuum.Payload.nonneg invoice
    inherited_bound := hInherited
    error := FundedCanonicalInputPayload.error R S
    error_paid := invoice
    calibration := C
    exponent := fun U => by
      have he := FundedCanonicalInputPayload.exponent R S P permits hG hw (A'.inputNorm m)
        (congrArg BudgetPoint.threshold hnorm) C hC U
      have hclip : P.bank.output.carrier.rep.clip = (R.family.path.levels.params (m+1)).clip := by
        rw [P.representation]
        rfl
      have hV : F'.layers = layers R M := eq_of_heq shared.vacuum
      have hr := rendered R M P.bank.output.carrier.rep.p U
      rw [← hV] at hr
      rw [← hclip, ← hr] at he
      exact he
    input := z
    multilinear := hLin
    input_retains := hKeep
    regularPrice := Retained.ordinaryRate K I 1
    forcedPrice := Pert.Asymptotics.regulatorRun R.family N t (m+1+1)^q
    forced_bound := hForced
    prepared := Q' }
  refine ⟨L,HEq.rfl,hz,hQ,rfl,rfl,rfl,?_⟩
  intro heta hI hOrd
  refine {
    original := P.bank.actual_forced
    reserved := ?_
    ordinary_nonnegative := ?_
    ordinary_small := hOrd }
  · change P.bank.output.carrier.rep.activities.KBound (A'.inputNorm m)
      (R.family.path.levels.clock.forcedAllowance (m+1))
    rw [hnorm]
    exact P.bank.fixed_forced
  · change 0 ≤ Retained.ordinaryRate K I 1
    rw [← ActualOrdinaryPriceMargins.rate_eq R K I]
    exact ActualOrdinaryPriceMargins.rate_nonnegative R K N t (m+1)
      I.inherited η I.regularPrice I.inherited_nonnegative heta hI.ordinary_nonnegative

end YM.Integration.WilsonLimitConstruction.FundedCanonicalReceiving
end
