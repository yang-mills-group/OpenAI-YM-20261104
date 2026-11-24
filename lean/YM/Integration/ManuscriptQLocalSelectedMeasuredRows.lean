import YM.Integration.ManuscriptQLocalMeasuredAffineRows
import YM.Integration.ManuscriptQLocalScalarProgramSelection

set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalSelectedMeasuredRows

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

open ManuscriptQLocalMeasuredAffineRows (measured)
open WilsonLimitConstruction Push.PriceCompiler FreeResolvent PhysicalNext.JointLoad Pressure.Tube
open PhysicalAffineScalarClockCost ConditionalCovarianceCutoff PhysicalAffineScalarFieldContraction
local notation "Pt" => query R.metals.p R.metals.K (i₁) (i₀)
local notation "Pe" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)

def At {order : ℕ→ℕ→ℕ} (paid : FundedPredictionSupply.Both
    (@ManuscriptQLocalScalarSourcePurchase.Paid G order) (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit) : Prop :=
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
      Root j s o (fun _ : PUnit.{1} => o) (fun _ => ManuscriptQLocalScalarFields.regular R d k q b Y₀ o) ((torusPay (PAC G 1) s)^j*ε) ∧
      Root j s o id (fun v => ManuscriptQLocalScalarFields.changedRoot R d k q b v (F' v) Y₀ 1 o)
        ((torusPay PUnit.{1} s*(torusPay (PAC G 1) s)^j)*ε) ∧
      ∀ (mode : Γ.Mode) (v : Fin j → Coarse),
        iteratedFDeriv ℝ j (fun B : Coarse => (Actual.Push Δ (P).beta Π (V B)).part mode/((P₀).eval (V B):ℂ)) 0 v =
        iteratedFDeriv ℝ j (measured R d D q H x k mode) 0 v
theorem measuredAt {order : ℕ→ℕ→ℕ} (paid : FundedPredictionSupply.Both
    (@ManuscriptQLocalScalarSourcePurchase.Paid G order) (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit) :
    At R d D q H x paid :=
  ManuscriptQLocalMeasuredAffineRows.original R d D q H x paid
end YM.Integration.ManuscriptQLocalSelectedMeasuredRows
end

noncomputable section
namespace YM.Integration.ManuscriptQLocalSelectedMeasuredRows
universe u
open Marker PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Push.SectorMeasure FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric LocalComparison

/-- A single attained campaign supplies the actual named measured affine-row
purchase on every one of its physical marked occurrences. -/
theorem original {G : Gauge} (simple : G.Simple) {penalty : ℝ} (hp : 0 < penalty)
    (order : ℕ → ℕ → ℕ) (extra : Prediction G) (funded : FundedPredictionSupply.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (paid : FundedPredictionSupply.Both (@ManuscriptQLocalScalarSourcePurchase.Paid G order)
        (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit),
      extra R.kit ∧
      (∀ {I : Type} [DecidableEq I] {Γ : Census I} (d : LocalFormal.Datum R.family Γ)
        (D : Allocation G (R.family.path.levels.clock.op d.level d.period) (R.alloy.B.a.clock.hatBeta d.level)
          (R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)))
        (q : Chi) [Fintype I] {J : Request I} {A : NumericSchedule R.family J}
        (H : AnalyticInput J A d) (x : TestSpace J.tests), At R d D q H x paid) ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple penalty W := by
  obtain ⟨R,T,W,paid,other,jets,corr,props⟩ :=
    ManuscriptQLocalScalarProgramSelection.attained_with_jets.{u} simple hp order (@extra) funded
  refine ⟨R,T,W,paid,other,?_,jets,corr,props⟩
  intro I inst Γ d D q fi J A H x
  exact measuredAt R d D q H x paid

end YM.Integration.ManuscriptQLocalSelectedMeasuredRows
end
