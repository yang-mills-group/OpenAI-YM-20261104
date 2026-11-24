import YM.Integration.WilsonRootedTwoDateRadialGallery
import YM.Integration.WilsonOriginalPointAmbient
import YM.Integration.WilsonOriginalPointPaidGallery

/-! Original ambient signed Wilson conditional as an actual multilinear point-source Taste at the first interior age. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateAmbientGallery
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

local notation "oldG" => regulatorRun R.family N p (m+2)
local notation "forcedRate" => Real.sqrt (R.alloy.B.a.clock.forcedAllowance (m+1))
local notation "ordinaryRate" => OriginalMarkedSpringBand.ordinary R (m+1) (Fintype.card V)

/-- One ambient independent-test presentation of the true normalized old conditional and all
its physical hard and ordinary invoices before any old test, at the actual newly occupied age. -/
def Realized (prev : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below) : Prop :=
  ∃ τ : ℝ,0<τ ∧ τ≤1 ∧ ∃ b : Overlay.Bands (Γ) (Y), b.origins=(step).ratio.parent ∘ old.roots ∧ b.units=0 ∧
    b.Active ∧ Seed.RadialReceipt b τ prev ∧
    let T := WilsonOriginalPointTaste.representation (tests) b
    Multilinear (tests) T ∧ FunctionalRetains T (fun v=>{b.origins v}) ∧
    (∀x U,old.ambient_response hG x U=((Y).eval U)⁻¹ • (T.leaf x).density U) ∧
    (∀x,WilsonOriginalPointTaste.Priced (tests) b (w:=fun _=>τ*1) (u:=0) (c:=ordinaryRate) (d:=(Real.sqrt 2*oldG)^(prev+1)) (b:=forcedRate) (paidLabels) x) ∧
    ∃ (s : ℝ),0<s ∧ s≤1 ∧ ∃ (I : Type) (_ : Fintype I) (a : I→Menu.Hat (Γ) (Y)),
      GapsLocal.Full.given a 0=b.density ∧ ∃ (K : Type) (_ : Fintype K) (f : K→Menu.Hat (Γ) (Y)),
      WilsonRootedTwoDateMenu.Combined R fresh.below P fresh.roots (fun _=>s) a f ∧
      ∀U,((Y).eval U)⁻¹ • GapsLocal.Full.given (Sum.elim a f) 0 U=(old.point_unit.response hG (Nat.le_succ (m+1)) U)*fresh.masked hG U

private theorem one_band (prev : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below) (visible : old.visible)
    (inlet : WilsonRootedTwoDateRadialGallery.Filed old.point_unit fresh hG prev P) : Realized old fresh hG prev P := by
  obtain ⟨τ,pos,one,b,roots,zero,live,paid,model,s,hs,s1,I,fi,a,reads,K,fk,f,joint,value⟩ := inlet
  have normalized (U) : old.point_unit.response hG (Nat.le_succ (m+1)) U=((Y).eval U)⁻¹ • b.density U := ((model U).2.2).trans (by rw [(model U).1])
  refine ⟨τ,pos,one,b,roots,zero,live,paid,WilsonOriginalPointTaste.multilinear (tests) b,WilsonOriginalPointTaste.retains (tests) b live,?_,WilsonOriginalPointTaste.paid (tests) b live paid (paidLabels) zero,s,hs,s1,I,fi,a,reads,K,fk,f,joint,?_⟩
  · intro x U
    funext k
    change (old.ambient_response hG x U).part k=(((Y).eval U)⁻¹ • ((WilsonOriginalPointTaste.representation (tests) b).leaf x).density U).part k
    have view := WilsonOriginalPointTaste.density (tests) b live paid (paidLabels) x U
    have coefficient := (congrArg (fun p : Poly (Γ)=>p.part k) view).trans (QlocalPageScaling.fuse_part _ (b.density U) k)
    rw [old.ambient_mode hG visible,normalized]
    change (∏i∈k.val,(x i).val 0)*((((Y).eval U)⁻¹:ℝ)*(b.density U).part k)=(((Y).eval U)⁻¹:ℝ)*(((WilsonOriginalPointTaste.representation (tests) b).leaf x).density U).part k
    rw [coefficient];exact mul_left_comm _ _ _
  · intro U
    exact (value U).trans (by rw [←(model U).2.2])

theorem original {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {Δ : Daisy.Charity.RG12.Decal G}
    (paid : FundedOriginalProperties.{u} hG ε W) (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (u v : V→MS.Rake.Label B) (prev now q : ℕ) {η : ℝ} (positive : 0<η) :
    ∀ᶠ m : ℕ in atTop,∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      Realized old fresh hG prev (ActualRunSpring.selected R N p m fresh.below) ∧
      ∀ x : IndependentTests (ActualOriginalQPointSetup.request R old.labels old.request).tests,
        Integrable (fun U=>Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U)) (scene R.family.path N p (m+1)) ∧
        ∫ U,Poly.price (oneW) (WilsonRootedTwoDateProduct.defect (old.with_test x) fresh hG U) ∂scene R.family.path N p (m+1) ≤ η*(regulatorRun R.family N p (m+1))^q := by
  filter_upwards [WilsonRootedTwoDateRadialGallery.original hG paid spring marks u v prev now q positive,eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)] with m issued after
  intro N p a f ha hf hr
  have visible : a.visible := by rw [Seed.visible,ha];omega
  exact ⟨one_band a f hG prev _ visible (issued N p a.point_unit f ha hf hr).1,fun x=>(issued N p (a.with_test x) f ha hf hr).2⟩

end YM.Integration.WilsonRootedTwoDateAmbientGallery
