import YM.Integration.QLocalInheritedPrincipalScroll
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quotes

/-! The genuine signed inherited singletons at the full pre-reset cover reserve. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.QLocalInheritedSourcePrice
open Function Finset Lattice Wilson Pressure RG Tree Precision Next Next.SectorChange
open AnalyticBridge VerifiedReset Collection LocalGaussian Push.AbsoluteSums Push.SectorMeasure
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir QLocalInheritedPrincipalScroll
open Marker Comparison.RG02 IterationFour IterationFour.Vacuum LocalComparison
open LocalComparison.Global FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open scoped BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
  (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
  {datum : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A datum}
  {η : ℝ} (I : FullPreparedInputAt F η)

def fee {n : ℕ} (J : Request V) (C : Libretto G n) (r : ℕ) : ℝ :=
  Classical.choose (Release.quoting C J.outputDistanceOrder r J.input_support_pos
    (show 0 ≤ J.outputSupport+3 by linarith [J.output_support_pos]))

omit [DecidableEq V] [Fintype V] in
theorem quote {n : ℕ} (J : Request V) (C : Libretto G n) (r : ℕ) :
    Release.Quotation C J.outputDistanceOrder r J.inputSupport (J.outputSupport+3) (fee J C r) :=
  Classical.choose_spec (Release.quoting C J.outputDistanceOrder r J.input_support_pos
    (show 0 ≤ J.outputSupport+3 by linarith [J.output_support_pos]))

local notation "p₀" => A.outputNorm datum.level
local notation "p₁" => A.inputNorm datum.level
local notation "S₀" => R.family.path.levels.clock.op datum.level datum.period
local notation "x₀" => R.family.path.levels.clock.hatBeta datum.level
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)
variable {l : ℕ}
local notation "L₀" => fun i => headed (S := S₀) (I.error.labels i) (x₀) l

theorem purchased {n r : ℕ} (C : Libretto G n) (hG : G.Simple)
    {Pt : Teller G} (T : Tube G (S₀)) (D : Heir.Record)
    (hT : Plays C D (p₀) (p₁) Pt T (x₀))
    (hA : Release.accepts r (p₁).supportExponent (Quotes.preExponent (p₀)) (S₀).patch.L)
    (hC : Lute.Plented C D (p₀) (p₁) (S₀).patch.L r (x₀) (g₁))
    (χ q : Chi) (d : ℝ) (hl : 500 ≤ l) (hr : l+5 ≤ r) :
    let hB : (p₀).B = radiusB (x₀) := (A.output_norm datum.level).block
    let σ := fun i => source (G:=G) (S₀) (p₁) (x₀) (g₁) D (I.error.labels i) χ l r
      (hB ▸ (p₀).B_pos) hl hr
    let principal := fun i => (σ i).tuning (g₁) q d (I.error.action i) T
    ∃ v : ℕ → ℝ, (∀ i, (p₀).Regular (L₀ i).support (principal i) ∧
      (p₀).supBounds (L₀ i).site (L₀ i).support (principal i) (v i)) ∧
      Quotes.early (p₀) (L₀) v (fee J C r/((S₀).patch.L.val:ℝ)*I.inherited) := by
  intro hB σ principal
  let a := { I.carrier.rep.activities with reg := I.error.labels, E := I.error.action }
  have ha : a.RegularFamily (p₁) := ⟨I.error_paid.smooth,I.error_paid.flat,I.error_paid.null⟩
  have hp : a.EBound (p₁) I.inherited := I.error_paid.credit
  have hq : Release.Quotation C (p₀).power r (p₁).supportExponent (Quotes.preExponent (p₀))
      (fee J C r) := by
    rw [(A.output_norm datum.level).distance,(A.input_norm datum.level).reserve,
      Quotes.preExponent,(A.output_norm datum.level).reserve]
    exact quote J C r
  have hg := Currency.g_pos R.makes datum.cutoff datum.period (datum.level+1) datum.below
  exact Release.chorus (a := a) (q := q) (d := d) σ (fun _ => rfl) hG hq hT hA hB hg.le hC
    (fun i => played (G:=G) _ _ _ _ _ (I.error.labels i) χ l r _ hl hr n hg) ha hp

end YM.Integration.QLocalInheritedSourcePrice
end
