import YM.Integration.PhysicalWilsonPeriodizedMaterial
import YM.Integration.WilsonLimitConstruction.FundedMatchedPointOpening

/-! The actual first Q law and its connected coefficients share the bare Wilson energy and signed probes. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalWilsonBornMaterial
open Function Filter Finset MeasureTheory Lattice Wilson RG Precision Marker Tree Exterior Multi
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep IterationFour IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Order Pert.Asymptotics ActualPolynomialContraction
open WilsonCoeffUV WilsonLimitConstruction FreeResolvent
open scoped Classical Topology BigOperators

variable {G:Gauge} {D:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V]
  (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label D) (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription D)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  (profile:∀k,k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
  (hm:ActualOriginalQInitialInput.start R hG u J A profile≤d.level)
  (hp:(ActualOriginalQPointSetup.request R u J).physicalPeriodLower≤(R.family.S.period d.period).val)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "F₀" => ActualOriginalQInitialInput.input R hG u J A d Q o μ orders profile hm hp
local notation "I₀" => ActualOriginalQInitialPreparation.input R hG u J A d Q o μ orders
local notation "Z" => FundedMatchedPointOpening.colors R hG u J A d Q o μ orders profile hm hp
local notation "P₁" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "g₁" => regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "K" => d.kernel (RunFormalChain.fromRun R)

omit [Fintype V] in
private theorem measured_bare {c f:Side} (step:StepData c f) (F:Forest step.ratio) {Γ:Census V}
    (W:Bulk.Colors Γ G f) (p:Clip) (P:PathData G) (O:ChartRatio G)
    (z:Bulk.Joint step F (G:=G)) :
    let X:=PhysicalWilsonJointMaterial.coordinates step F z
    let U:=mantle X
    W.vac z.1 U=Wilson.energy U-mainTerm p P U →
    z.1^2*Precision.loop P U=0 →
    PhysicalWilsonJointMaterial.measured step F W p P O z=
      Wilson.energy U+jointPen G step (Sum.elim X (flatten z.2.1))-
        z.1^2*Real.log (∏i:F.Free,O.J (z.2.2 i)):=by
  intro X U hvac hloop
  change mainTerm p P U+jointPen G step (Sum.elim X (flatten z.2.1))+
    z.1^2*(Precision.loop P U-unhaar O X)+W.vac z.1 U+
    z.1^2*(unhaar O X-Real.log (∏i:F.Free,O.J (z.2.2 i)))=_
  rw [hvac]
  linear_combination hloop

theorem bare (top:d.cutoff=d.level+1) (t:TestSpace (J₀).tests) (F:Forest (S).ratio)
    (z:Bulk.Joint (S) F (G:=G)):
    let X:=PhysicalWilsonJointMaterial.coordinates (S) F z
    let U:=mantle X
    PhysicalWilsonJointMaterial.measured (S) F (Z t) (P₁).clip (P₁).path R.metals.O z=
      Wilson.energy U+jointPen G (S) (Sum.elim X (flatten z.2.1))-
        z.1^2*Real.log (∏i:F.Free,R.metals.O.J (z.2.2 i)):=by
  intro X U
  apply measured_bare (S) F (Z t) (P₁).clip (P₁).path R.metals.O z
  · change Wilson.energy U-
        mainTerm (R.family.path.rep (d.level+1) d.period (d.level+1)).clip
          (R.family.path.rep (d.level+1) d.period (d.level+1)).path U=_
    rw [top]
  · rw [top]
    exact WilsonCompensatedOpening.dormant R d.level d.period z.1 U

theorem charged (t:TestSpace (J₀).tests) (g:ℝ) (hg:g≠0) (U:Config G (R.family.side (d.level+1) d.period)):
    Integral.markedLog g U (Z t)=(ActualOriginalQInitialInput.packets R hG u J A d Q o μ orders).read t g U:=
  (F₀).convention.marks t g hg U

theorem issued [Nonempty V] (top:d.cutoff=d.level+1) (ref:ActualOriginalQLayout.referenceLevel R u≤d.level+1)
    (t:TestSpace (J₀).tests) (B:fieldDir G (R.family.side d.level d.period) 1) (r:ℕ)
    (F:Forest (S).ratio) (tag:(S).Choices):
    ((I₀).leaf t).density=Integral.model g₁ 0 (Z t) (K) ∧
      Bulk.Fk (K) F tag (Z t) B r=PhysicalWilsonPeriodizedMaterial.reference
        R d.cutoff d.level d.period d.below B (Z t) r ∧
      ∀s:(Board (Stock.census V) r).Mode,(logMarked (Bulk.Fk (K) F tag (Z t) B r)).part s=
        (logMarked (PhysicalWilsonPeriodizedMaterial.reference R d.cutoff d.level d.period
          d.below B (Z t) r)).part s:=by
  have hw:=FundedMatchedPointOpening.well R hG u J A d Q o μ orders profile hm hp t
  exact ⟨FundedMatchedPointOpening.density R hG u J A d Q o μ orders profile hm hp top ref t,
    PhysicalWilsonPeriodizedMaterial.original R d.cutoff d.level d.period d.below B (Z t) r F tag hw,
    PhysicalWilsonPeriodizedMaterial.connected R d.cutoff d.level d.period d.below B (Z t) r F tag hw⟩

end YM.Integration.PhysicalWilsonBornMaterial
end
