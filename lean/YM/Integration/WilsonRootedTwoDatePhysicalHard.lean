import YM.Integration.WilsonRootedTwoDateAmbientGallery
import YM.Integration.WilsonRootedTwoDateIndependentHard

/-! The funded old point comparison and independently tested complete fresh hard insertion on its physical band. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDatePhysicalHard
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence WilsonRootedTwoDateProduct OPE.Therm
open WilsonLimitConstruction Push.AbsoluteSums.Animals RG.Shoot Pert.Asymptotics
open scoped Classical Topology BigOperators
universe u
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ}
local notation "Y" => R.family.path.rep N p (m+1)
local notation "Γ" => Stock.census V
local notation "step" => R.family.path.levels.clock.op (m+1) p
local notation "oneW" => fun _ : V=>(1:ℝ)
variable (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m) (hG : G.Simple)

local notation "tests" => (ActualOriginalQPointSetup.request R old.labels old.request).tests

/-- One radius and one historical band carry the original old response and both funded hard families. -/
def Paid (prev : ℕ) : Prop :=
    ∃τ : ℝ, 0<τ ∧ τ≤1 ∧ ∃b : Overlay.Bands (Γ) (Y),
      b.origins=fresh.roots ∧ b.units=0 ∧ b.Active ∧ Seed.RadialReceipt b τ prev ∧
      (∀x U,old.ambient_response hG x U=((Y).eval U)⁻¹ •
        ((WilsonOriginalPointTaste.representation (tests) b).leaf x).density U) ∧
      WilsonRootedTwoDateForcedRegistration.Registered fresh hG b ∧
      WilsonRootedTwoDateIndependentHard.Enrolled fresh hG (tests) b

private theorem attach (prev : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below)
    (layout : fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots)
    (original : WilsonRootedTwoDateAmbientGallery.Realized old fresh hG prev P) :
    Paid old fresh hG prev := by
  obtain ⟨τ,ht,one,b,roots,units,active,radial,_,_,read,_⟩ := original
  have same : b.origins=fresh.roots := roots.trans layout.symm
  exact ⟨τ,ht,one,b,same,units,active,radial,read,
    WilsonRootedTwoDateForcedRegistration.current fresh hG b same active radial,
    WilsonRootedTwoDateIndependentHard.original fresh hG (tests) b same active radial⟩

theorem original {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {Δ : Daisy.Charity.RG12.Decal G}
    (paid : FundedOriginalProperties.{u} hG ε W) (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (u v : V→MS.Rake.Label B) (prev now q : ℕ) {η : ℝ} (positive : 0<η) :
    ∀ᶠ m : ℕ in atTop,∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      WilsonRootedTwoDateAmbientGallery.Realized old fresh hG prev (ActualRunSpring.selected R N p m fresh.below) ∧
      Paid old fresh hG prev ∧
      ∀ x : IndependentTests (ActualOriginalQPointSetup.request R old.labels old.request).tests,
        Integrable (fun U=>Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U)) (scene R.family.path N p (m+1)) ∧
        ∫ U,Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U) ∂scene R.family.path N p (m+1) ≤ η*(regulatorRun R.family N p (m+1))^q := by
  filter_upwards [WilsonRootedTwoDateAmbientGallery.original hG paid spring marks u v prev now q positive] with m bought
  intro N p old fresh h₁ h₂ layout
  obtain ⟨band,bound⟩ := bought N p old fresh h₁ h₂ layout
  exact ⟨band,attach old fresh hG prev _ layout band,bound⟩

end YM.Integration.WilsonRootedTwoDatePhysicalHard
