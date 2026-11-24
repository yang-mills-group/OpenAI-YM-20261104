import YM.Integration.WilsonRootedTwoDateRadial
import YM.Integration.WilsonOriginalPointPush

/-! The complete inherited physical gallery and the new OPE join on the exact same lower Wilson field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateRadialGallery
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

/-- The physical joint catalogue retains the actual old hard gas and the original all-mode radial bound. -/
def Filed (prev : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below) : Prop :=
  ∃ τ : ℝ,0<τ ∧ τ≤1 ∧ ∃ b : Overlay.Bands (Γ) (Y), b.origins=(step).ratio.parent ∘ old.roots ∧ b.units=0 ∧
    ∃ (active : b.Active) (radial : Seed.RadialReceipt b τ prev),
    let A := WilsonRetainedMarkedInlet.incoming b active radial (paidLabels)
    (∀U,A.density () U=b.density U ∧ A.gas () U=b.cluster U ∧ old.response hG (Nat.le_succ (m+1)) U=((Y).eval U)⁻¹ • A.density () U) ∧
    ∃ (s : ℝ),0<s ∧ s≤1 ∧ ∃ (I : Type) (_ : Fintype I) (a : I→Menu.Hat (Γ) (Y)),
      GapsLocal.Full.given a 0=b.density ∧ ∃ (K : Type) (_ : Fintype K) (f : K→Menu.Hat (Γ) (Y)),
      WilsonRootedTwoDateMenu.Combined R fresh.below P fresh.roots (fun _=>s) a f ∧
      ∀U,((Y).eval U)⁻¹ • GapsLocal.Full.given (Sum.elim a f) 0 U=(((Y).eval U)⁻¹ • A.density () U)*fresh.masked hG U

theorem registered {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G} (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (prev now : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below)
    (one : GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2))
    (two : GapsLocal.Full.target 0 (Fintype.card V) now ≤ R.alloy.B.a.clock.J (m+1))
    (room : Fintype.card V≤R.alloy.B.a.clock.J (m+1)) (sites : ∀s : ActualOriginalQReaders.Slot old.labels,R.family.ref s.2.size ≤ m+2)
    (roots : fresh.roots=(step).ratio.parent ∘ old.roots) : Filed old fresh hG prev P := by
  obtain ⟨τ,hτ,hτ',b,transfer,org,zero,live,radial,booked⟩ := old.radial hG spring marks prev now one two sites
  obtain ⟨positive,upper,I,finite,a,_,read,alone,_⟩ := booked
  let δ := QLocalFullRootedOffer.radius 1 (OriginalMarkedBandSuccessor.ceiling R m (Fintype.card V) prev)
  let s := δ*τ
  have hs : 0<s := mul_pos positive hτ
  have hs' : s≤1 := (mul_le_mul_of_nonneg_left hτ' positive.le).trans (by simpa using upper)
  have op : Menu.Offer b.origins a (fun _=>s) (Y).p.B ((Y).p.supportExponent-4) 1 := by simpa only [mul_one] using alone
  have ofresh := (congrArg (fun z=>Menu.Offer z a (fun _=>s) (Y).p.B ((Y).p.supportExponent-4) 1) (org.trans roots.symm)).mp op
  obtain ⟨funded,thin,f,joint,survives⟩ := fresh.native_joint hG spring room P a s hs hs' ofresh
  have normalized (U) : old.response hG (Nat.le_succ (m+1)) U=((Y).eval U)⁻¹ • b.density U := by rw [old.pushed hG,transfer]
  let A := WilsonRetainedMarkedInlet.incoming b live radial (paidLabels)
  have readA (U) : A.density () U=b.density U := WilsonRetainedMarkedInlet.original b live radial (paidLabels) zero U
  refine ⟨τ,hτ,hτ',b,org,zero,live,radial,fun U=>⟨readA U,WilsonRetainedMarkedInlet.forced b live radial (paidLabels) U,(readA U).symm ▸ normalized U⟩,_,funded,thin,I,finite,a,read,_,inferInstance,f,joint,?_⟩
  intro U
  rw [survives,read,readA,mul_comm (fresh.masked hG U),smul_mul_assoc]

theorem original {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {Δ : Daisy.Charity.RG12.Decal G}
    (paid : FundedOriginalProperties.{u} hG ε W) (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (u v : V→MS.Rake.Label B) (prev now q : ℕ) {η : ℝ} (positive : 0<η) :
    ∀ᶠ m : ℕ in atTop,∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      Filed old fresh hG prev (ActualRunSpring.selected R N p m fresh.below) ∧
      Integrable (fun U=>Poly.price (oneW) (WilsonRootedTwoDateProduct.defect old fresh hG U)) (scene R.family.path N p (m+1)) ∧
      ∫ U,Poly.price (oneW) (WilsonRootedTwoDateProduct.defect old fresh hG U) ∂scene R.family.path N p (m+1) ≤η*(regulatorRun R.family N p (m+1))^q := by
  filter_upwards [WilsonRootedFirstInteriorCarry.eventually_ready R prev now u,WilsonRootedTwoDateProduct.cooled hG paid u v q positive] with m clocks small
  intro N p a f ha hf roots
  have sites : ∀s : ActualOriginalQReaders.Slot a.labels,R.family.ref s.2.size ≤ m+2 := by rw [ha];exact fun s=>(clocks.2.2.2 s).trans (Nat.le_succ _)
  exact ⟨registered a f hG spring marks prev now _ clocks.1 clocks.2.1 clocks.2.2.1 sites roots,small N p a f ha hf⟩

end YM.Integration.WilsonRootedTwoDateRadialGallery
