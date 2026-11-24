import YM.Integration.FullQLocalCanonicalForcedOutput

/-! A literal packet catalogue and chain plan carry the complete pre-reset
and post-reset physical data. Both analytic action conventions use this
same two-representation interface. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedRenderedBank
open Filter Lattice Wilson RG Marker MeasureTheory
open RG3.Script.Picnic Comparison.RG02
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : Census V}
    {C : Family G} {J : Request V} {A : NumericSchedule C J} {d : LocalFormal.Datum C B}
    {F : AnalyticInput J A d} {η : ℝ}

structure Catalogue (J : Request V) (d : LocalFormal.Datum C B) where
  model : MarkedPackets J.tests G (C.side d.level d.period) B
  plan : Plan C d.cutoff d.period J.order

def previous {Y : Bulk.Chain C.path} {caps : Handoff.OutputCapacities} {K : NumericPrices A}
    (M : AnalyticOutput caps Y K F) : Catalogue J d := ⟨M.model,M.plan⟩

structure Bank (I : FullPreparedInputAt F η) (M : Catalogue J d) where
  output : ProducedOutput J.tests I.carrier F.fineRoots F.coarseRoots I.input
  same_model : output.model = M.model
  wellFormed : WellFormed (A.outputNorm d.level) output.carrier.rep
  actual_forced : output.carrier.rep.activities.KBound
    (C.path.levels.budget d.level) (C.path.levels.clock.forcedAllowance d.level)
  fixed_forced : output.carrier.rep.activities.KBound
    (A.outputNorm d.level) (C.path.levels.clock.forcedAllowance d.level)
  output_active x : (output.output.leaf x).Active
  formal_active x : (output.formalAligned.leaf x).Active
  output_multilinear : Multilinear J.tests output.output
  formal_multilinear : Multilinear J.tests output.formalAligned
  residual_multilinear : Multilinear J.tests output.residual
  output_retains : FunctionalRetains output.output F.outputAddresses
  formal_retains : FunctionalRetains output.formalAligned F.outputAddresses
  residual_retains : FunctionalRetains output.residual F.outputAddresses
  aligned : QlocalMarkedPrimaryProposal.AlignedRegularRows
    output.output output.formalAligned output.residual
  primary : Retained.ChosenPrimary output

structure Pre (K : NumericPrices A) (I : FullPreparedInputAt F η) (M : Catalogue J d) (bank : Bank I M) where
  listing : AnalyticBridge.VerifiedReset.Collection.Listing G
    (C.side d.level d.period)
  source : AnalyticBridge.VerifiedReset.Collection.Source G
    (C.side d.level d.period)
  scalar : ℝ
  estimate : AnalyticBridge.VerifiedReset.Collection.Local listing
    (A.outputNorm d.level) source
    (vacuumRate J.order K.vacuumConstant (C.S.block d.level).val
      (K.vanishing d.level) (K.geometry d.level) I.inherited η
      (Currency.g C d.cutoff d.period (d.level + 1)))
    (C.path.levels.clock.forcedAllowance d.level)
  representation : bank.output.carrier.rep =
    PreReset.append (M.plan.layers d.level)
      (C.path.rep d.cutoff d.period d.level).path
      (C.path.levels.params d.level).clip (C.path.levels.budget d.level)
      listing source (M.plan.predict d.level) scalar 0
      (Render.prefactor (Currency.gain (M.plan.predict d.level)))

structure Chosen (K : NumericPrices A) (I : FullPreparedInputAt F η) (M : Catalogue J d) where
  bank : Bank I M
  vacuum : Pre K I M bank

variable {K : NumericPrices A} {I : FullPreparedInputAt F η} {M : Catalogue J d}

def reclosed (S : Chosen K I M) : Rep G (C.side d.level d.period) :=
  Render.append (M.plan.layers d.level)
    (Reset.after
      (C.path.rep d.cutoff d.period d.level).path
      (C.path.levels.params d.level).clip
      (C.path.levels.budget d.level)
      S.vacuum.listing S.vacuum.source
      (M.plan.predict d.level) S.vacuum.scalar 0)
    (Render.prefactor (Currency.gain (M.plan.predict d.level)))

structure Canonical (S : Chosen K I M) where
  bank : Bank I M
  representation : bank.output.carrier.rep=reclosed S

theorem Canonical.reserve {S : Chosen K I M} (P : Canonical S) :
    (reclosed S).activities.KBound (C.path.levels.budget d.level) (C.path.levels.clock.forcedAllowance d.level) := by
  rw [←P.representation]
  exact P.bank.actual_forced

theorem Canonical.densities {S : Chosen K I M} (P : Canonical S) (x : TestSpace J.tests) :
    (P.bank.output.output.leaf x).density=(S.bank.output.output.leaf x).density :=
  (P.bank.output.density x).symm.trans (S.bank.output.density x)

structure Bounds (K : NumericPrices A) (I : FullPreparedInputAt F η) (M : Catalogue J d)
    (S : Bank I M) (delta : ℝ) (forcedOrder : ℕ) where
  connected : Retained.ZeroChannels I → QlocalMarkedPrimaryProposal.IndependentConnectedClause J.tests
    (A.outputNorm d.level) S.output.residual F.outputRadii
    (envelopeProduct F.kernelCosts)
    (markedRate J.order delta (K.markedConstant delta) (K.geometry d.level)
      I.inherited η
      (Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level + 1)))
  residual_price : RelativeBudget (A.outputNorm d.level)
    (pullback (testInclusion J.tests) S.output.residual) F.outputRadii
    (forcedDivisor C d.level) (envelopeProduct F.kernelCosts)
    (Retained.ordinaryRate K I delta)
    ((Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level + 1)) ^
      forcedOrder)
  primary : S.primary.Bound
    (Retained.ordinaryRate K I delta)
  forced : ForcedBudget (A.outputNorm d.level)
    (priceNormalized (envelopeProduct F.kernelCosts)
      (pullback (testInclusion J.tests) S.output.output)) F.outputRadii
    (forcedDivisor C d.level)
    ((Pert.Asymptotics.regulatorRun C d.cutoff d.period (d.level + 1)) ^
      forcedOrder)

/- Pull both genuine physical representations and their numerical bounds out
of any given legacy witness. The physical fields and selected roots are literal. -/
section Legacy
variable {Y : Bulk.Chain C.path} {caps : Handoff.OutputCapacities} {N : AnalyticOutput caps Y K F}

def before (S : Retained.Chosen K I N) : Chosen K I (previous N) :=
  let bank : Bank I (previous N) := ⟨S.output,S.same_model,S.wellFormed,S.actual_forced,S.fixed_forced,
    S.output_active,S.formal_active,S.output_multilinear,S.formal_multilinear,S.residual_multilinear,
    S.output_retains,S.formal_retains,S.residual_retains,S.aligned,S.primary⟩
  ⟨bank,⟨S.vacuum.listing,S.vacuum.source,S.vacuum.scalar,S.vacuum.estimate,S.vacuum.representation⟩⟩

def after {S : Retained.Chosen K I N} (P : Numeric.Canonical.CanonicalOutput S) : Canonical (before S) :=
  let bank : Bank I (previous N) := ⟨P.output,P.same_model,P.wellFormed,P.actual_forced,P.fixed_forced,
    P.output_active,P.formal_active,P.output_multilinear,P.formal_multilinear,P.residual_multilinear,
    P.output_retains,P.formal_retains,P.residual_retains,P.aligned,P.primary⟩
  ⟨bank,P.representation⟩

def before_bounds {S : Retained.Chosen K I N} {δ : ℝ} {f : ℕ} (h : Retained.Bounds S δ f) :
    Bounds K I (previous N) (before S).bank δ f :=
  ⟨h.connected,h.residual_price,h.primary,h.forced⟩

def after_bounds {S : Retained.Chosen K I N} {P : Numeric.Canonical.CanonicalOutput S} {δ : ℝ} {f : ℕ}
    (h : Numeric.Canonical.CanonicalBounds P δ f) : Bounds K I (previous N) (after P).bank δ f :=
  ⟨h.connected,h.residual_price,h.primary,h.forced⟩

def recover (S : Chosen K I (previous N)) : Retained.Chosen K I N := by
  let b := S.bank
  let v := S.vacuum
  exact ⟨b.output,b.same_model,b.wellFormed,b.actual_forced,b.fixed_forced,b.output_active,
    b.formal_active,b.output_multilinear,b.formal_multilinear,b.residual_multilinear,b.output_retains,
    b.formal_retains,b.residual_retains,b.aligned,⟨v.listing,v.source,v.scalar,v.estimate,v.representation⟩,b.primary⟩

def recover_canonical {S : Chosen K I (previous N)} (P : Canonical S) : Numeric.Canonical.CanonicalOutput (recover S) :=
  let b := P.bank
  ⟨b.output,P.representation,b.same_model,b.wellFormed,b.actual_forced,b.fixed_forced,b.output_active,
    b.formal_active,b.output_multilinear,b.formal_multilinear,b.residual_multilinear,b.output_retains,
    b.formal_retains,b.residual_retains,b.aligned,b.primary⟩

def recover_bounds {S : Chosen K I (previous N)} {δ : ℝ} {f : ℕ}
    (h : Bounds K I (previous N) S.bank δ f) : Retained.Bounds (recover S) δ f :=
  ⟨h.connected,h.residual_price,h.primary,h.forced⟩

def recover_canonical_bounds {S : Chosen K I (previous N)} {P : Canonical S} {δ : ℝ} {f : ℕ}
    (h : Bounds K I (previous N) P.bank δ f) : Numeric.Canonical.CanonicalBounds (recover_canonical P) δ f :=
  ⟨h.connected,h.residual_price,h.primary,h.forced⟩

end Legacy
end YM.Integration.WilsonLimitConstruction.FundedRenderedBank
end
