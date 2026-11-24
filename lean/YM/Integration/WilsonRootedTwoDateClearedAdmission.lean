import YM.Integration.WilsonRootedTwoDateOldIdentity
import YM.Integration.WilsonRootedTwoDateCooledMenu
import YM.Integration.WilsonRootedTwoDateCooling

/-! A complete earlier insertion meets a separately submitted, genuine later insertion
on the original physical lower law and the same native spring. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateClearedAdmission
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

/-- The recovered native pupil reads the full inherited signed band times the actual cooled fresh insertion. -/
def Admitted (P : ActualRunSpring.Packet R N p m fresh.below) : Prop :=
  ∃ b : Overlay.Bands (Γ) (Y), b.origins=(step).ratio.parent ∘ old.roots ∧ b.units=0 ∧ b.Active ∧
    (∀U,old.response hG (Nat.le_succ (m+1)) U=((Y).eval U)⁻¹ • b.density U) ∧
    ∃ (s : ℝ),0<s ∧ s≤1 ∧ ∃ (I : Type) (_ : Fintype I) (a : I→Menu.Hat (Γ) (Y)),
      GapsLocal.Full.given a 0=b.density ∧ ∃ (K : Type) (_ : Fintype K) (f : K→Menu.Hat (Γ) (Y)),
      WilsonRootedTwoDateMenu.Combined R fresh.below P fresh.roots (fun _=>s) a f ∧
      ∀U,((Y).eval U)⁻¹ • GapsLocal.Full.given (Sum.elim a f) 0 U=
        old.response hG (Nat.le_succ (m+1)) U*fresh.masked hG U

/-- One actual higher source builds the band which finances the joined physical pupil. -/
theorem registered {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G} (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (prev now : ℕ) (P : ActualRunSpring.Packet R N p m fresh.below)
    (one : GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2))
    (two : GapsLocal.Full.target 0 (Fintype.card V) now ≤ R.alloy.B.a.clock.J (m+1))
    (room : Fintype.card V≤R.alloy.B.a.clock.J (m+1)) (sites : ∀s : ActualOriginalQReaders.Slot old.labels,R.family.ref s.2.size ≤ m+2)
    (roots : fresh.roots=(step).ratio.parent ∘ old.roots) : Admitted old fresh hG P := by
  obtain ⟨τ,hτ,hτ',b,transfer,org,zero,live,booked⟩ := old.carry hG spring marks prev now one two sites
  obtain ⟨positive,upper,I,finite,a,_,read,alone,_⟩ := booked
  let δ := QLocalFullRootedOffer.radius 1 (OriginalMarkedBandSuccessor.ceiling R m (Fintype.card V) prev)
  let s := δ*τ
  have hs : 0<s := mul_pos positive hτ
  have hs' : s≤1 := (mul_le_mul_of_nonneg_left hτ' positive.le).trans (by simpa using upper)
  have op : Menu.Offer b.origins a (fun _=>s) (Y).p.B ((Y).p.supportExponent-4) 1 := by simpa only [mul_one] using alone
  have ofresh := (congrArg (fun z=>Menu.Offer z a (fun _=>s) (Y).p.B ((Y).p.supportExponent-4) 1) (org.trans roots.symm)).mp op
  obtain ⟨funded,thin,f,joint,survives⟩ := fresh.native_joint hG spring room P a s hs hs' ofresh
  have normalized (U) : old.response hG (Nat.le_succ (m+1)) U=((Y).eval U)⁻¹ • b.density U := by rw [old.pushed hG,transfer]
  refine ⟨b,org,zero,live,normalized,_,funded,thin,I,finite,a,read,_,inferInstance,f,joint,?_⟩
  intro U
  rw [survives,read,normalized,mul_comm (fresh.masked hG U),smul_mul_assoc]

/-- The bought lower-date kernel is genuinely integrable and its difference from the complete
unmasked joint physical field is arbitrarily small, uniformly over the submitted data. -/
theorem original {ε : ℝ} {T : Campaign R} {W : Campaign.Pillars R T} {Δ : Daisy.Charity.RG12.Decal G}
    (paid : FundedOriginalProperties.{u} hG ε W) (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay)
    (u v : V→MS.Rake.Label B) (prev now q : ℕ) {η : ℝ} (positive : 0<η) :
    ∀ᶠ m : ℕ in atTop,∀ N p (old : Seed R B V N p (m+1)) (fresh : Seed R B V N p m),old.labels=u → fresh.labels=v →
      fresh.roots=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots →
      Admitted old fresh hG (ActualRunSpring.selected R N p m fresh.below) ∧
      Integrable (fun U=>Poly.price (oneW) (WilsonRootedTwoDateProduct.defect old fresh hG U)) (scene R.family.path N p (m+1)) ∧
      ∫ U,Poly.price (oneW) (WilsonRootedTwoDateProduct.defect old fresh hG U) ∂scene R.family.path N p (m+1) ≤η*(regulatorRun R.family N p (m+1))^q := by
  filter_upwards [WilsonRootedFirstInteriorCarry.eventually_ready R prev now u,WilsonRootedTwoDateProduct.cooled hG paid u v q positive] with m clocks small
  intro N p a f ha hf roots
  have sites : ∀s : ActualOriginalQReaders.Slot a.labels,R.family.ref s.2.size ≤ m+2 := by rw [ha];exact fun s=>(clocks.2.2.2 s).trans (Nat.le_succ _)
  exact ⟨registered a f hG spring marks prev now _ clocks.1 clocks.2.1 clocks.2.2.1 sites roots,small N p a f ha hf⟩

end YM.Integration.WilsonRootedTwoDateClearedAdmission
