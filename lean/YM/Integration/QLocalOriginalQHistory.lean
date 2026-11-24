import YM.Integration.QLocalOriginalQEnvelope
import YM.Integration.QLocalOriginalQState

/-! A physical Q source receipt records its original test orbit, period and
upper cutoff through every genuine selected successor. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalOriginalQHistory

open Filter Lattice Wilson RG Marker Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 FullQLocal.PreRun.SuccessiveRequests WilsonLimitConstruction QLocalReceivedWilsonState
open MergeProof.Accent
open scoped Classical Topology

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V] {B:MS.Local.Physical.Deck G}
    (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B)
    (J₀:Request V) (A₀:NumericSchedule R.family J₀)
    (d₀:LocalFormal.Datum R.family (Stock.census V)) (P₀:MS.Land.Prescription B)
    (o:V→Site (R.family.side (d₀.level+1) d₀.period)) (μ:ℝ) (orders:V→ℕ)
local notation "D₀" => FullQLocal.RenderedStep.Request.tests (ActualOriginalQPointSetup.request R u J₀)
local notation "T₀" => ActualOriginalQInitialPreparation.input R hG u J₀ A₀ d₀ P₀ o μ orders

structure Origin {J:Request V} {d:LocalFormal.Datum R.family (Stock.census V)} {A:NumericSchedule R.family J}
    {F:AnalyticInput J A d} {η:ℝ} (I:FullPreparedInputAt F η) : Prop where
  cutoff : d.cutoff=d₀.cutoff
  period : d.period=d₀.period
  tests : J.tests=(D₀)
  replay : ∃ source:TestSpace J.tests → Config G (R.family.side (d₀.level+1) d.period)→Poly (Stock.census V),
    State I (d₀.level+1) source ∧ ∀ (t:TestSpace J.tests) (t₀:TestSpace (D₀)), HEq t t₀ →
      HEq (source t) (((T₀).leaf t₀).density)

local notation "Origin₀" => Origin R hG u J₀ A₀ d₀ P₀ o μ orders

theorem start {A':NumericSchedule R.family (ActualOriginalQPointSetup.request R u J₀)}
    {F:AnalyticInput (ActualOriginalQPointSetup.request R u J₀) A' d₀} {η:ℝ} {I:FullPreparedInputAt F η}
    (L:State I (d₀.level+1) (fun t=>((T₀).leaf t).density)) : (Origin₀) I := by
  refine ⟨rfl,rfl,rfl,_,L,?_⟩
  intro t t₀ h
  exact heq_of_eq (congrArg (fun x=>((T₀).leaf x).density) (eq_of_heq h))

omit [DecidableEq V] [Fintype V] [Nonempty V] in
private theorem scaled {D E:V → ComparisonDensity.Address.Orbit} (types:D=E) (a:V→ℂ)
    {t:TestSpace D} {t₀:TestSpace E} (h:HEq t t₀) :
    HEq (VariableScaling.tests a t) (VariableScaling.tests a t₀) := by
  subst E
  exact heq_of_eq (congrArg (VariableScaling.tests a) (eq_of_heq h))

theorem unit {V:Type} [DecidableEq V] [Fintype V] {D E:V → ComparisonDensity.Address.Orbit} (types:D=E) (t:IndependentTests D) :
    ∃ t₀:IndependentTests E, HEq (testInclusion D t) (testInclusion E t₀) := by
  subst E
  exact ⟨t,HEq.rfl⟩

omit [Fintype V] [Nonempty V] in
private theorem same {C:Family G} {k j N N' a b:ℕ} {Γ:Census V}
    {X:Config G (C.side j a)→Poly Γ} {X':Config G (C.side j b)→Poly Γ}
    (cut:N=N') (per:a=b) (h:HEq X X') (hk:k≤j) :
    HEq (gust C.path N a j X k hk) (gust C.path N' b j X' k hk) := by
  subst N' b
  exact heq_of_eq (congrArg (fun x=>gust C.path N a j x k hk) (eq_of_heq h))

variable {J:Request V} {d:LocalFormal.Datum R.family (Stock.census V)} {A:NumericSchedule R.family J}
    {F:AnalyticInput J A d} {η:ℝ} {I:FullPreparedInputAt F η}

/-- The complete output, evaluated on the restored tests, is the true
transport of the unscaled physical Q field from its original upper cutoff. -/
theorem physical (H:(Origin₀) I) (M:FundedRenderedBank.Catalogue J d) (S:FundedRenderedBank.Bank I M)
    (t:TestSpace J.tests) (t₀:TestSpace (D₀)) (ht:HEq t t₀) :
    let h:=ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ P₀ o μ orders
    let Q:=ActualOriginalQInput.input P₀
      (ActualOriginalQPointSetup.pointDatum R J₀ d₀.period (d₀.level+1) o) u (μ-R.family.S.scale d₀.cutoff)
      orders hG d₀.cutoff d₀.below
    ∃ hk:d.level≤d₀.level+1, HEq (S.output.output.leaf (VariableScaling.tests (fun _=>(h:ℂ)) t)).density
      (gust R.family.path d₀.cutoff d₀.period (d₀.level+1) (Q.leaf t₀).density d.level hk) := by
  obtain ⟨source,state,assign⟩:=H.replay
  let a:V→ℂ:=fun _=>(ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ P₀ o μ orders:ℂ)
  have e:=assign _ _ (scaled H.tests a ht)
  have realfield:=funext (QLocalOriginalQEnvelope.original R hG u J₀ A₀ d₀ P₀ o μ orders t₀)
  have hk:d.level≤d₀.level+1:=(Nat.le_succ _).trans state.before
  exact ⟨hk,(heq_of_eq (QLocalReceivedWilsonState.output state M S (VariableScaling.tests a t))).trans
    (same H.cutoff H.period (e.trans (heq_of_eq realfield)) hk)⟩

variable {K:NumericPrices A} {caps:Handoff.OutputCapacities} {M:FundedPhysicalCatalogue.Purchase caps K F}
    {S:FundedRenderedBank.Chosen K I M.toCatalogue} {P:FundedRenderedBank.Canonical S}
    {m r q:ℕ} {hm:d.level=m+1} {A':NumericSchedule R.family (nextRequest J caps r)}
    {W:Bulk.Colors (Stock.census V) G (R.family.side (m+1) d.period)}
    {x:Exterior.fieldDir G (R.family.side m d.period) 1}
    {Z:FundedCoverStepPrice.Receipt R M S P r hm A' W x q}

theorem issued (H:(Origin₀) I) (next:FundedCoverFlatStep.Accepted R Z) : (Origin₀) next.input := by
  obtain ⟨source,st,assign⟩:=H.replay
  exact ⟨H.cutoff,H.period,H.tests,source,QLocalReceivedWilsonState.issued R st next,assign⟩

end YM.Integration.QLocalOriginalQHistory
