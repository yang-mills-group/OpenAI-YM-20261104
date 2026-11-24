import YM.Integration.QLocalRetainedSourceAncestor
import YM.Integration.ActualRunSpring
import YM.IterationFour.Running
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Choirs

/-! The chosen prepared vacuum's genuine inherited payload supplies the
value, affine cancellation, derivative bounds, and original anchored credit
for the native principal singleton station on the actual physical block. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.QLocalInheritedPrincipal
open Function Finset Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange
open Next.SectorChange.Rows Exterior Bloch Planned.AtomRegular
open AnalyticBridge.LocalGaussian Push.AbsoluteSums Push.SectorMeasure
open MultiNext.SignedSource MultiNext.SignedSource.Mom
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir PhysicalNext.Repeat.Legato
open Marker Comparison.RG02 IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
  (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
  {datum : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A datum}
  {η : ℝ} (I : FullPreparedInputAt F η)

local notation "p₀" => A.outputNorm datum.level
local notation "p₁" => A.inputNorm datum.level
local notation "S₀" => R.family.path.levels.clock.op datum.level datum.period
local notation "x₀" => R.family.path.levels.clock.hatBeta datum.level
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)
local notation "o₁" => fun i => (I.error.labels i).site
local notation "X₁" => fun i => (I.error.labels i).support

theorem seed (i : ℕ) : Seed (p₁) (o₁ i) (X₁ i) (I.error.action i) :=
  ⟨I.error_paid.smooth i,(I.error.labels i).anchor,I.error_paid.flat i,I.error_paid.null i⟩

theorem four (hG : G.Simple) (i : ℕ) (hn : 4 ≤ (R.family.side (datum.level+1) datum.period).val)
    (hX : Nonwrapping (X₁ i) (o₁ i)) :
    Mediator.valence (fun j => (Mom.Maps (o₁ i) (X₁ i) j (G := G) : Set _)) 4
      (I.error.action i ∘ increment 1) := (seed R I i).four hG hX hn

theorem inputs :
    ∃ v : ℕ → ℝ, (∀ i, Seed (p₁) (o₁ i) (X₁ i) (I.error.action i) ∧
      (p₁).supBounds (o₁ i) (X₁ i) (I.error.action i) (v i)) ∧
      ∀ z, SumBudget (fun i => if o₁ i = z then (p₁).mass (X₁ i) (v i) else 0) I.inherited := by
  obtain ⟨v,hv,hp⟩ := I.error_paid.credit
  exact ⟨v,fun i => ⟨seed R I i,hv i⟩,hp⟩

def fee {n : ℕ} (J : Request V) (C : Libretto G n) (r : ℕ) : ℝ :=
  Classical.choose (Release.quoting C J.outputDistanceOrder r J.input_support_pos J.output_support_pos.le)

omit [DecidableEq V] [Fintype V] in
theorem quote {n : ℕ} (J : Request V) (C : Libretto G n) (r : ℕ) :
    Release.Quotation C J.outputDistanceOrder r J.inputSupport J.outputSupport (fee J C r) :=
  Classical.choose_spec (Release.quoting C J.outputDistanceOrder r J.input_support_pos J.output_support_pos.le)

theorem principal {n r : ℕ} (C : Libretto G n) (hG : G.Simple)
    {D : Heir.Record} {Pt : Teller G} (T : Tube G (S₀))
    (hT : Plays C D (p₀) (p₁) Pt T (x₀))
    (hA : Release.accepts r (p₁).supportExponent (p₀).supportExponent (S₀).patch.L)
    (hB : (p₀).B = radiusB (x₀))
    (hC : Lute.Plented C D (p₀) (p₁) (S₀).patch.L r (x₀) (g₁))
    (labels : ℕ → RegularAddress (R.family.side datum.level datum.period))
    (σ : ∀ i, Script G (S₀) (X₁ i) (labels i).support r (x₀))
    (hs : ∀ i, (labels i).site = (S₀).ratio.parent (o₁ i))
    (hh : ∀ i, (σ i).Played n (g₁) (D.ε*(p₁).threshold)) (q : Chi) (d : ℝ) :
    ∃ v : ℕ→ℝ, (∀ i, let f := (σ i).tuning (g₁) q d (I.error.action i) T
      (p₀).Regular (labels i).support f ∧ (p₀).supBounds (labels i).site (labels i).support f (v i)) ∧
      Footprint.Anchored (fun i => (labels i).site) v (fun i => coverNumber (p₀).B (labels i).support)
        (p₀).supportExponent (fee J C r/((S₀).patch.L.val:ℝ)*I.inherited) := by
  let a := { I.carrier.rep.activities with reg := I.error.labels, E := I.error.action }
  have ha : a.RegularFamily (p₁) := ⟨I.error_paid.smooth,I.error_paid.flat,I.error_paid.null⟩
  have hp : a.EBound (p₁) I.inherited := I.error_paid.credit
  have hq : Release.Quotation C (p₀).power r (p₁).supportExponent (p₀).supportExponent (fee J C r) := by
    rw [(A.output_norm datum.level).distance,(A.input_norm datum.level).reserve,
      (A.output_norm datum.level).reserve]
    exact quote J C r
  have hg : 0 ≤ g₁ := (Currency.g_pos R.makes datum.cutoff datum.period (datum.level+1) datum.below).le
  exact Release.chorus (a := a) (q := q) (d := d) σ hs hG hq hT hA hB hg hC hh ha hp

end YM.Integration.QLocalInheritedPrincipal
end
