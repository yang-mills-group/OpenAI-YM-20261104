import YM.Integration.ManuscriptQLocalScalarFields
import YM.Integration.ManuscriptQLocalScalarProgramSelection

/-! One physical run pays the Gaussian field comparison to every fixed finite order.
The lower stage is chosen before the cutoff, torus period, changed forest and test directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalCofinalAffineFields
open Marker Function Filter Lattice Wilson RG RG.Shoot Tree Pressure Pressure.Testing Pressure.Tube Pressure.Stores
open Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark PhysicalAffineScalarFieldContraction
open PhysicalNext.JointLoad PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe WilsonLimitConstruction
open PhysicalAffineScalarClockCost ConditionalCovarianceCutoff Push.PriceCompiler
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

open ManuscriptQLocalScalarFields WilsonLimitConstruction.FundedCompanySelection
universe u

def schedule (nextStage _previousStage : ℕ) : ℕ := nextStage

abbrev Paid {G : Gauge} (R : Run G) :=
  FundedPredictionSupply.Both (@ManuscriptQLocalScalarSourcePurchase.Paid G schedule)
    (@ManuscriptQLocalScalarClockPurchase.Paid G schedule) R.kit

section
variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "P₀" => Clockwork.patch R.rolls (step_paid R.alloy.B.a d.level) (first_le R.alloy.B.valid d.level)


/-- Both multilinear forms use the clock allowance already chosen for this stage. -/
def Contracted (paid : Paid R) (through : ℕ) : Prop :=
    let n := j₁
    let r := paid.1.choose (j₁) (j₀)
    let K := (Pt).bind
    let p := (Pt).top.clip
    let a := (Pt).top.paths
    let b := (Pt).top.width
    let P := (P₀)
    let κ := ManuscriptQLocalScalarClockPurchase.cutoff (Pt) P.L
    let δ := ManuscriptQLocalGaussianRootPrice.fixedWidth G P K p (Pt) n r.spatial
    let M := ManuscriptQLocalGaussianRootPrice.sourcePrice G (Pt) P.L n
    let s := min δ (width G P K p (n+1) a b)/2
    let geo := allowance G P K p n a b δ r.ordinary r.discarded M
    let ε := geo*Real.exp (-(κ/2)*(till θ:ℝ))
    0<s ∧ 0<κ/2 ∧ ∀ (k : (S).Choices) (q : Chi) (b : ℝ)
    (F' : ∀ tag : Site c₀, {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : ∀ tag, LinkArray G (Frozen A θ (F' tag).val)) (o : Site c₀)
    (j : ℕ), j≤through →
    Root j s o (fun _ : PUnit.{1} => o) (fun _ => regular R d k q b Y o)
      ((torusPay (PAC G 1) s)^j*ε) ∧
    Root j s o id (fun tag => changedRoot R d k q b tag (F' tag) Y (Z tag) o)
      ((torusPay PUnit.{1} s*(torusPay (PAC G 1) s)^j)*ε)

theorem row (paid : Paid R) (through : ℕ) (adequate : through ≤ j₁) :
    Contracted R d paid through := by
  obtain ⟨hs, hk, used⟩ := ManuscriptQLocalScalarFields.original R d paid
  refine ⟨hs, hk, ?_⟩
  intro k q price forests held changed site j degree
  exact used k q price forests held changed site j (degree.trans adequate)
end

/-- Every tested order has one lower stage on the same physical run. -/
theorem cofinal {G : Gauge} (R : Run G) (paid : Paid R) (through : ℕ) :
    ∃ first : ℕ, ∀ (I : Type) [DecidableEq I] (Γ : Census I) (d : LocalFormal.Datum R.family Γ),
      first ≤ d.level → Contracted R d paid through := by
  have deep : Tendsto R.alloy.B.a.clock.J atTop atTop := R.family.path.levels.fits.deep
  obtain ⟨first, ready⟩ := eventually_atTop.mp (deep.eventually_ge_atTop through)
  exact ⟨first, fun _ _ _ d eligible =>
    row R d paid through (ready (d.level+1) (eligible.trans (Nat.le_succ _)))⟩

def All {G : Gauge} (R : Run G) (paid : Paid R) : Prop :=
  ∀ through : ℕ, ∃ first : ℕ, ∀ (I : Type) [DecidableEq I] (Γ : Census I)
    (d : LocalFormal.Datum R.family Γ), first ≤ d.level → Contracted R d paid through

/-- The original existence construction buys the field estimates and the other filed prediction together. -/
theorem attained {G : Gauge} (simple : G.Simple) {penalty : ℝ} (hp : 0 < penalty)
    (extra : Prediction G) (funded : FundedPredictionSupply.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T) (paid : Paid R),
      extra R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple penalty W ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      All R paid := by
  obtain ⟨R,T,W,paid,other,jets,corr,original⟩ :=
    ManuscriptQLocalScalarProgramSelection.attained_with_jets.{u} simple hp schedule (@extra) funded
  exact ⟨R,T,W,paid,other,corr,original,jets,cofinal R paid⟩

theorem original {G : Gauge} (simple : G.Simple) {penalty : ℝ} (hp : 0 < penalty) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T) (paid : Paid R),
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple penalty W ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧ All R paid := by
  obtain ⟨R,T,W,paid,corr,original⟩ :=
    ManuscriptQLocalScalarProgramSelection.original.{u} simple hp schedule
  exact ⟨R,T,W,paid,corr,original,ManuscriptQLocalScalarProgramSelection.measuredOn R,cofinal R paid⟩

end YM.Integration.ManuscriptQLocalCofinalAffineFields
end


