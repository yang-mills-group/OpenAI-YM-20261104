import YM.Integration.WilsonRootedTwoDateHardSubpower

/-! The least site tariff of the actual two signed previous menus on the band which is pushed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateOldInvoice
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof MergeProof.Accent Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence WilsonRootedTwoDateProduct
open private input_leaf from YM.Integration.ActualOriginalQInitialPreparation
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ} (old : Seed R B V N p (m+1)) (hG : G.Simple)
local notation "topRep" => R.family.path.rep N p (m+2)
local notation "loRep" => R.family.path.rep N p (m+1)
local notation "upperStep" => R.family.path.levels.clock.op (m+1) p

local notation "Γ" => Stock.census V
local notation "oldG" => Pert.Asymptotics.regulatorRun R.family N p (m+2)
local notation "oneW" => fun _ : V=>(1:ℝ)

open scoped BigOperators

/-- The same finite nonnegative incidence sum used in the physical rooted offer. -/
def sitePrice {n : Side} {P : Rep G n} {I : Type} [Fintype I] (q : I → Menu.Hat (Stock.census V) P) : ℝ :=
  QLocalPhysicalBirthMenu.sitePrice (fun i=>(q i).M.crest) P.p.B (fun i=>Menu.fare (q i) (fun _=>1)) (P.p.supportExponent-4)

abbrev Slots := Bool × ActualRunFullPages.Index (ActualOriginalQInput.atomPositions
  (ActualOriginalQPointSetup.pointDatum R old.request p (m+2) old.roots) old.labels)

def Paid (b : Overlay.Bands (Γ) (loRep)) (τ fee : ℝ) : Prop :=
  (∃q : Slots old → Menu.Hat (Γ) (topRep), old.numerator hG=GapsLocal.Full.given q 0 ∧
    (upperStep).push (topRep).beta (old.numerator hG)=b.density ∧
    Menu.Offer old.roots q (oneW) (topRep).p.B ((topRep).p.supportExponent-4) fee ∧ sitePrice q=fee ∧
    ∀other:ℝ, Menu.Offer old.roots q (oneW) (topRep).p.B ((topRep).p.supportExponent-4) other → fee≤other) ∧
  0≤fee ∧ τ⁻¹=1+fee

theorem registered {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G} (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay) (prev : ℕ)
    (one : GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2))
    (sites : ∀s : ActualOriginalQReaders.Slot old.labels,R.family.ref s.2.size ≤ m+2) :
    ∃ τ : ℝ, 0<τ ∧ τ≤1 ∧ ∃ b : Overlay.Bands (Γ) (loRep),
      (upperStep).push (topRep).beta (old.numerator hG)=b.density ∧ b.origins=(upperStep).ratio.parent ∘ old.roots ∧
      b.units=0 ∧ b.Active ∧ Seed.RadialReceipt b τ prev ∧ ∃fee : ℝ, Paid old hG b τ fee := by
  let D := ActualOriginalQPointSetup.pointDatum R old.request p (m+2) old.roots
  let x := testInclusion (ActualOriginalQPointSetup.request R old.labels old.request).tests old.test
  let c := ActualOriginalQInitialInput.scales R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree
  let o := (ActualOriginalQPackets.positions D old.labels).origin
  have same : o=old.roots := funext fun i=>ActualOriginalQPointDatum.root_eq R _ _ _ _ _ i
  let P := ActualRunSpring.selected R N p (m+1) old.below
  have stock : Menu.Arsenal (topRep) := Mallow.Many.sharp (A:=R.alloy) (m:=m+1) (n:=p) (Q:=fun _=>(topRep)) P.point (RunPhysicalMarks.actual_hasSlots R N p (m+2) old.below)
  obtain ⟨family,all⟩ := WilsonOriginalOPEPageMenu.realized old.prescription D old.labels (old.scale-R.family.S.scale N) old.degree hG N old.below sites stock (oneW) (fun _=>zero_lt_one)
  let X := VariableScaling.tests c x
  obtain ⟨read,_,offered⟩ := all X
  let q := family X
  let fee := sitePrice q
  have trueOffer : Menu.Offer o q (oneW) (topRep).p.B ((topRep).p.supportExponent-4) fee :=
    ⟨offered.sites,QLocalPhysicalBirthMenu.hit _ _ _ _ (fun _=>Menu.Crew (oneW) (fun _=>zero_lt_one))⟩
  have cost0 : 0≤fee := Push.AbsoluteSums.budget_nonneg (trueOffer.budget 0)
  let τ := QLocalFullRootedOffer.radius 1 fee
  obtain ⟨pos,leone,limited⟩ := QLocalFullRootedOffer.limited o (oneW) (fun _=>zero_lt_one) q 1 zero_lt_one ((topRep).p.supportExponent-4) (topRep).p.B trueOffer
  have reserve := (ManuscriptQLocalMarkedGradeTail.campaign R spring).2 0
  have occurs : Extra.Multi.Occupancy ((upperStep).ratio.parent ∘ o) (R.family.path.levels.clock.J (m+2)) := by
    have count : Fintype.card V ≤ GapsLocal.Full.target 0 (Fintype.card V) prev := by unfold GapsLocal.Full.target; omega
    exact fun _=>(Finset.card_le_univ _).trans (count.trans one)
  obtain ⟨b,_,_,pushed,shares,roots,live,_,_,paid,_,_,_⟩ := OriginalMarkedSpringBand.received R hG old.below marks
    (reserve.trans (R.alloy.B.a.fits.deepExp (Nat.zero_le _))) (reserve.trans (R.alloy.B.a.fits.deepExp (Nat.zero_le _)))
    one o (fun _=>τ*1) (fun _=>mul_pos pos zero_lt_one) occurs (family X) limited
  have source := congrArg (fun leaf=>leaf.density) (input_leaf R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree x)
  have hn : old.numerator hG=GapsLocal.Full.given (family X) 0 := source.trans read
  have lower : 1/(1+fee)≤1 := (div_le_one (by linarith)).mpr (by linarith)
  have inverse : τ⁻¹=1+fee := by
    rw [show τ=min 1 (1/(1+|fee|)) from rfl,abs_of_nonneg cost0,min_eq_right lower,one_div,inv_inv]
  have deposit : (upperStep).push (topRep).beta (old.numerator hG)=b.density := hn.symm ▸ pushed
  refine ⟨τ,pos,leone,b,deposit,roots.trans (congrArg ((upperStep).ratio.parent ∘ ·) same),shares.units.1,live,paid,fee,?_,cost0,inverse⟩
  refine ⟨q,hn,deposit,?_,rfl,?_⟩
  · exact same ▸ trueOffer
  · intro other alt
    exact QLocalPhysicalBirthMenu.least _ _ _ _ alt.budget

end YM.Integration.WilsonRootedTwoDateOldInvoice
