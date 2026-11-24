import YM.Integration.WilsonRootedTwoDateRadialGallery

/-! One full signed carrier, with the same old gauge field, before all physical upper tests. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDatePointGallery
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

local notation "paidLabels" => (R.makes.wilson.represents N p (m+1) fresh.below).good.labels

local notation "tests" => (ActualOriginalQPointSetup.request R old.labels old.request).tests

/-- The same complete, radial lower band represents every bounded old test on its original
physical slot, with genuine before-test coefficient and complete hard inventory. -/
def Common (prev : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below) : Prop :=
  ∃ τ : ℝ,0<τ ∧ τ≤1 ∧ ∃ b : Overlay.Bands (Γ) (Y), b.origins=(step).ratio.parent ∘ old.roots ∧ b.units=0 ∧
    ∃ (active : b.Active) (radial : Seed.RadialReceipt b τ prev),
    let A := WilsonRetainedMarkedInlet.incoming b active radial (paidLabels)
    (∀U,A.density () U=b.density U ∧ A.gas () U=b.cluster U) ∧
    (∀ (x : IndependentTests (tests)) (k : (Γ).Mode), ‖∏ i∈k.val,(x i).val 0‖≤1 ∧ ∀U,
      ((old.with_test x).response hG (Nat.le_succ (m+1)) U).part k=
        (∏ i∈k.val,(x i).val 0)*(((Y).eval U)⁻¹ • A.density () U).part k) ∧
    ∃ (s : ℝ),0<s ∧ s≤1 ∧ ∃ (I : Type) (_ : Fintype I) (a : I→Menu.Hat (Γ) (Y)),
      GapsLocal.Full.given a 0=b.density ∧ ∃ (K : Type) (_ : Fintype K) (f : K→Menu.Hat (Γ) (Y)),
      WilsonRootedTwoDateMenu.Combined R fresh.below P fresh.roots (fun _=>s) a f ∧
      ∀U,((Y).eval U)⁻¹ • GapsLocal.Full.given (Sum.elim a f) 0 U=(((Y).eval U)⁻¹ • A.density () U)*fresh.masked hG U

private theorem one_band (prev : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below) (visible : old.visible)
    (inlet : WilsonRootedTwoDateRadialGallery.Filed old.point_unit fresh hG prev P) : Common old fresh hG prev P := by
  obtain ⟨τ,pos,one,b,roots,zero,live,paid,model,menu⟩ := inlet
  refine ⟨τ,pos,one,b,roots,zero,live,paid,fun U=>⟨(model U).1,(model U).2.1⟩,?_,menu⟩
  intro x k
  refine ⟨old.mode_bound x k,?_⟩
  intro U
  rw [old.response_mode hG visible x k U,(model U).2.2]

theorem original {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {Δ : Daisy.Charity.RG12.Decal G}
    (paid : FundedOriginalProperties.{u} hG ε W) (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (u v : V→MS.Rake.Label B) (prev now q : ℕ) {η : ℝ} (positive : 0<η) :
    ∀ᶠ m : ℕ in atTop,∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      Common old fresh hG prev (ActualRunSpring.selected R N p m fresh.below) ∧
      ∀ x : IndependentTests (ActualOriginalQPointSetup.request R old.labels old.request).tests,
        Integrable (fun U=>Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U)) (scene R.family.path N p (m+1)) ∧
        ∫ U,Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U) ∂scene R.family.path N p (m+1) ≤ η*(regulatorRun R.family N p (m+1))^q := by
  filter_upwards [WilsonRootedTwoDateRadialGallery.original hG paid spring marks u v prev now q positive,eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)] with m issued after
  intro N p a f ha hf hr
  have visible : a.visible := by rw [Seed.visible,ha];omega
  exact ⟨one_band a f hG prev _ visible (issued N p a.point_unit f ha hf hr).1,fun x=>(issued N p (a.with_test x) f ha hf hr).2⟩

end YM.Integration.WilsonRootedTwoDatePointGallery
