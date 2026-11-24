import YM.Integration.ManuscriptQLocalMeasuredConditional
import YM.Integration.ManuscriptQLocalScalarFields

/-! The original weighted scalar field results together with the actual conditional field derivatives. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMeasuredAffineRows

open Function Filter MeasureTheory Matrix Lattice Wilson RG RG.Shoot Supply Input Precision Marker Multi Exterior Tree Pressure
open Next.SectorChange Gaussian Pressure.Testing Pressure.Stores
open Push.SectorMeasure Push.SectorMeasure.Oriented Push.SectorMeasure.Presented Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent.Affine
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Integral Actual
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "Θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => Pressure.Testing.ships R.alloy.B d.cutoff d.level d.period
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "A₀" => noHole Δ
local notation "J₀" => R.metals.O
local notation "i₀" => R.alloy.B.a.clock.J d.level
local notation "i₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "w" => R.kit.walls i₁ i₀
local notation "b" => radiusW R.kit.rider i₁ i₀ * R.alloy.B.a.clock.threshold (d.level+1)
local notation "Coarse" => Gaussian.Vec (Raw G (R.family.side d.level d.period))
local notation "Fine" => Config G (R.family.side (d.level+1) d.period)
local notation "V" => fun B : Coarse => represent (decode B)
variable (D : Allocation G (R.family.path.levels.clock.op d.level d.period) (R.alloy.B.a.clock.hatBeta d.level)
  (R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) (q : Chi)

local notation "W" => shots Δ Θ
local notation "F" => d.forest
local notation "Y₀" => (1 : LinkArray G (Frozen A₀ Θ F))

variable [Fintype I] {J : Request I} {A : NumericSchedule R.family J} (H : AnalyticInput J A d) (x : TestSpace J.tests)
local notation "Π" => ManuscriptQLocalActualLog.source R d H x
local notation "u" => fun s : Γ.Mode => Actual.atMark s Π

abbrev measured (k₀ : (Δ).Choices) (s : Γ.Mode) (B : Coarse) : ℂ :=
  ManuscriptQLocalMeasuredConditional.measured R d D q H x k₀ s B

theorem conditional_jet (k₀ : (Δ).Choices) (s : Γ.Mode) (j : ℕ) (v : Fin j→ Coarse) :
    iteratedFDeriv ℝ j (fun B : Coarse => (Actual.Push Δ (P).beta Π (V B)).part s/((P₀).eval (V B):ℂ)) 0 v =
      iteratedFDeriv ℝ j (measured R d D q H x k₀ s) 0 v := ManuscriptQLocalMeasuredConditional.conditional_jet R d D q H x k₀ s j v

theorem joint_jet (k₀ : (Δ).Choices) {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (t : Z) (field : Z→ Coarse) (hc : ContinuousAt field t) (h₀ : field t=0)
    (tests : Z→ TestSpace J.tests) (mode : Γ.Mode) (j : ℕ) (v : Fin j→ Z) :
    let source := fun z => ManuscriptQLocalActualLog.source R d H (tests z)
    iteratedFDeriv ℝ j (fun z => (Actual.Push Δ (P).beta (source z) (V (field z))).part mode/((P₀).eval (V (field z)):ℂ)) t v =
      iteratedFDeriv ℝ j (fun z => measured R d D q H (tests z) k₀ mode (field z)) t v := ManuscriptQLocalMeasuredConditional.joint_jet R d D q H k₀ t field hc h₀ tests mode j v

open WilsonLimitConstruction Push.PriceCompiler FreeResolvent PhysicalNext.JointLoad Pressure.Tube
open PhysicalAffineScalarClockCost ConditionalCovarianceCutoff PhysicalAffineScalarFieldContraction
local notation "Pt" => query R.metals.p R.metals.K (i₁) (i₀)
local notation "Pe" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)

/-- Complete scalar comparison on the same physical signed/quiet stage.
Every independently rooted dense field contraction and all field derivatives
of the true conditional use the same no-hole draw, fine temperature,
licensed cutoff, undisturbed insertion, and retained hole complement. -/
theorem original {order : ℕ→ℕ→ℕ} (paid : FundedPredictionSupply.Both
    (@ManuscriptQLocalScalarSourcePurchase.Paid G order) (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit) :
    let n := order (i₁) (i₀)
    let r := paid.1.choose (i₁) (i₀)
    let K := (Pt).bind
    let clip := (Pt).top.clip
    let a := (Pt).top.paths
    let width₀ := (Pt).top.width
    let patch := (Pe)
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (Pt) patch.L
    let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G patch K clip (Pt) n r.spatial
    let M := ManuscriptQLocalGaussianRootPrice.sourcePrice G (Pt) patch.L n
    let s := min δ (width G patch K clip (n+1) a width₀)/2
    let geo := allowance G patch K clip n a width₀ δ r.ordinary r.discarded M
    let ε := geo*Real.exp (-(κ/2)*(till Θ:ℝ))
    0<s ∧ 0<κ/2 ∧ ∀ (k : (Δ).Choices)
      (F' : ∀ tag : Site (R.family.side d.level d.period),{U : Forest (Δ).ratio // FreeResolvent.Affine.changed Δ F U tag})
      (o : Site (R.family.side d.level d.period)) (j : ℕ), j≤n →
      Root j s o (fun _ : PUnit => o) (fun _ => ManuscriptQLocalScalarFields.regular R d k q b Y₀ o) ((torusPay (PAC G 1) s)^j*ε) ∧
      Root j s o id (fun v => ManuscriptQLocalScalarFields.changedRoot R d k q b v (F' v) Y₀ 1 o)
        ((torusPay PUnit s*(torusPay (PAC G 1) s)^j)*ε) ∧
      ∀ (mode : Γ.Mode) (v : Fin j → Coarse),
        iteratedFDeriv ℝ j (fun B : Coarse => (Actual.Push Δ (P).beta Π (V B)).part mode/((P₀).eval (V B):ℂ)) 0 v =
        iteratedFDeriv ℝ j (measured R d D q H x k mode) 0 v := by
  intro n r K clip a width₀ patch κ δ M s geo ε
  obtain ⟨hs,hκ,h⟩ := ManuscriptQLocalScalarFields.original R d paid
  refine ⟨hs,hκ,?_⟩; intro k F' o j hj
  have prices := h k q b F' Y₀ (fun _ => 1) o j hj
  exact ⟨prices.1,prices.2,fun mode v => ManuscriptQLocalMeasuredConditional.conditional_jet R d D q H x k mode j v⟩

end YM.Integration.ManuscriptQLocalMeasuredAffineRows
end
