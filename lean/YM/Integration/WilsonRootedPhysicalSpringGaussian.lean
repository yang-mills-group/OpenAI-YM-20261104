import YM.Integration.WilsonRootedPhysicalSpringElection
import YM.Integration.ManuscriptQLocalGaussianRootPrice

/-! The physical spring and Gaussian square share their original campaign and scalar source. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.WilsonRootedPhysicalSpringGaussian

section Stage
open ManuscriptQLocalGaussianRootPrice
open Marker Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarCutWeights PhysicalAffineScalarCutResidual PhysicalAffineScalarGaussianWeights
open PhysicalAffineScalarRootContraction PhysicalAffineScalarResidualVectors PhysicalAffineScalarResidualPrice
open PhysicalAffineScalarOperatorPrices ConditionalAffineLoadPrices ConditionalAffineForcing
open PhysicalAffineScalarAperture (noHole)
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "θ" => R.alloy.B.a.clock.hatBeta d.level
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "A" => noHole S
local notation "c₀" => R.family.side d.level d.period
local notation "Coarse" => Gaussian.Vec (Raw G c₀)
local notation "rows" => Rows.Receipt G S
local notation "rpos" => PhysicalAffineScalarComparison.rowRoot (G:=G) S
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K (j₁) (j₀)
local notation "ρ" => ConditionalAffineSourcePrices.rate (Pt) (S).patch.L
local notation "a₀" => (Pt).top.paths
local notation "b₀" => (Pt).top.width

/-- The two native rooted estimates use the fees selected by this same source payment. -/
def Gaussian (order : ℕ → ℕ → ℕ) (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit) : Prop :=
    let n := order (j₁) (j₀)
    let r := paid.choose (j₁) (j₀)
    let u₀ := ConditionalAffineLoadPrices.fullFee G (S).patch.L n r.ordinary r.discarded ρ θ
    let κ := min ρ (b₀/4)
    let δ := fixedWidth G (S).patch (S).kernel (T).high (Pt) n r.spatial
    let M := sourcePrice G (Pt) (S).patch.L n
    0<δ ∧ 0<M ∧ 0<κ ∧ ∀ (k : (S).Choices) (q : Chi) (b : ℝ) (tag : Site c₀)
    (F' : {U : Forest (S).ratio // changed S d.forest U tag})
    (Y : LinkArray G (Frozen A θ d.forest)) (Z : LinkArray G (Frozen A θ F'.val)) (g : ℝ) (o : Site c₀)
    (l : List (raw G c₀)), l.length≤n →
      (ContDiffAt ℝ n (ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o) 0 ∧
      (marks G c₀ δ).pay l o * ((native c₀).weight δ o tag *
        |jet (ray G c₀) (ManuscriptQLocalRootPrice.error R d k q b tag F' Y Z g o) l 0|) ≤
      prefactor G (S).patch (S).kernel (T).high n a₀ b₀ δ (u₀+|slip| * M) u₀ (|slip| * M) g *
        Real.exp (-κ*(till θ:ℝ))) ∧
      (ContDiffAt ℝ n (squareGap T θ k d.forest q b Y g o) 0 ∧
       (marks G c₀ δ).pay l o*|jet (ray G c₀) (squareGap T θ k d.forest q b Y g o) l 0|≤
       prefactor G (S).patch (S).kernel (T).high n a₀ b₀ δ (u₀+|slip| * M) u₀ (|slip| * M) g *
         Real.exp (-κ*(till θ:ℝ))) 
end Stage

open Filter Lattice Wilson RG RG.Supply Precision Org Push.PriceCompiler
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open FullQLocal FullQLocal.RenderedStep WilsonOriginalMarkedExistence
open scoped Classical Topology
open private purchase from YM.Integration.WilsonRootedPhysicalSpringElection
universe u
variable {G : Gauge} {V : Type}

/-- The physical OPE spring and marked height, together with the charged square at every stage. -/
structure Receipt [Fintype V] (hG : G.Simple) (ε : ℝ) (J : Request V) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (order : ℕ → ℕ → ℕ) (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
    (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit) : Prop where
  calendar : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit
  orders : ∀ i, i ≤ (R.metals.p.profile i).order ∧ i ≤ (R.metals.p.profile i).power
  spring : R2I.Funded ((Mallow.orbitD G).paired (garment10 G)) R T
  height : Mallow.RG12.Earned (ManuscriptQLocalMarkedHeightRun.acquisition G J) R.kit.shape R.alloy.delay
  salary : WilsonOriginalHighSelection.Salary G R.kit
  light : Stationary.LightPath R.alloy.B.kin Real.log
  marker : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay
  checkout : Mallow.RG12.Earned (GapsLocal.Renew.checkout G) R.kit.shape R.alloy.delay
  correlations : NativeFVAPlateau.Correlations R
  original : FundedOriginalProperties.{u} hG ε W
  charged : Charged R
  gaussian : ∀ {I : Type} [DecidableEq I] {Γ : Marker.Census I} (d : LocalFormal.Datum R.family Γ),
    Gaussian R d order paid

/-- An additional original prepaid menu is accepted before the physical spring election. -/
theorem selectedWith [Fintype V] (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (order : ℕ → ℕ → ℕ)
    (prediction : Prediction G) (price : FundedPredictionSupply.AllPrices (@prediction)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit),
      prediction R.kit ∧ Receipt.{u} hG ε J extra γ order R T W paid := by
  let stock := @FundedPredictionSupply.Both G (@prediction) (@ManuscriptQLocalScalarSourcePurchase.Paid G order)
  let calendar := @QLocalRequestedSectorCalendar.Paid G V J (WilsonRootedJointCalendar.scheme G J) extra γ
  let joint := @FundedPredictionSupply.Both G (@stock) (@calendar)
  obtain ⟨R,T,W,pred,orders,spring,height,cor,original⟩ := purchase.{u} J hG hε
    (@FundedPredictionSupply.Both G (@FundedPredictionSupply.Both G
      (@FundedPredictionSupply.Both G (@joint) (@WilsonOldActionForecast.Eligible G))
      (@WilsonOriginalHighSelection.Salary G)) (@WilsonOriginalLightSelection.Lit G Real.log))
    (fun s t => WilsonOriginalLightSelection.ordinary Real.log (WilsonOriginalHighSelection.ordinary
      (FundedPredictionSupply.both (FundedPredictionSupply.both
        (FundedPredictionSupply.both (price s t)
          (ManuscriptQLocalScalarSourcePurchase.prepaid order s (ThroughLaunch.raging s t)))
        (QLocalRequestedSectorCalendar.prepaid J (WilsonRootedJointCalendar.scheme G J)
          extra γ hG hγ s (ThroughLaunch.raging s t)))
        (WilsonOriginalMarkedExistence.prepaid s (ThroughLaunch.raging s t)))))
  obtain ⟨⟨⟨⟨⟨request,paid⟩,booked⟩,eligible⟩,salary⟩,light⟩ := pred
  obtain ⟨marker,checkout⟩ := WilsonOldActionForecast.issued R eligible
  refine ⟨R,T,W,paid,request,⟨booked,orders,spring,height,salary,light,marker,checkout,cor,original,
    OriginalMarkedGibbsRate.charged R hG,?_⟩⟩
  intro I _ Γ d
  exact ManuscriptQLocalGaussianRootPrice.original R d paid

/-- The original scalar source, calendar, physical orbit and height are jointly purchasable. -/
theorem selected [Fintype V] (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) (order : ℕ → ℕ → ℕ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (paid : ManuscriptQLocalScalarSourcePurchase.Paid order R.kit),
      Receipt.{u} hG ε J extra γ order R T W paid := by
  obtain ⟨R,T,W,paid,_,receipt⟩ := selectedWith.{u} hG hε J extra γ hγ order
    (@FundedPredictionSupply.Always G) (fun s t => FundedPredictionSupply.always s (ThroughLaunch.raging s t))
  exact ⟨R,T,W,paid,receipt⟩

end YM.Integration.WilsonRootedPhysicalSpringGaussian
end
