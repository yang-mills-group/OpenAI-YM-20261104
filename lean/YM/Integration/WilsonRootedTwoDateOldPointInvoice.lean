import YM.Integration.WilsonRootedTwoDateOldInvoice
import YM.Integration.WilsonRootedOPEPointPrice

/-! The earlier full Wilson OPE input is purchased before the upper cutoff and the physical torus. -/
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateOldPointInvoice
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

open WilsonRootedTwoDateOldInvoice

def phase : ℝ :=
  let D := ActualOriginalQPointSetup.pointDatum R old.request p (m+2) old.roots
  let x := testInclusion (ActualOriginalQPointSetup.request R old.labels old.request).tests old.test
  let c := ActualOriginalQInitialInput.scales R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree
  let X := VariableScaling.tests c x
  WilsonRootedOPEPhase.wallet (fun s : ActualOriginalQReaders.Slot old.labels=>
    ActualOriginalQReaders.readers old.prescription D old.labels (old.scale-R.family.S.scale N) old.degree s (X s.1))

theorem registered (u : V→MS.Rake.Label B) {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G}
    (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay) :
    ∀ᶠ m : ℕ in atTop, ∃cash : ℝ, 0≤cash ∧ ∀(N p : ℕ) (old : Seed R B V N p (m+1)), old.labels=u →
      ∀ (prev : ℕ), GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2) →
      ∃ τ : ℝ, 0<τ ∧ τ≤1 ∧ ∃ b : Overlay.Bands (Γ) (R.family.path.rep N p (m+1)),
        (R.family.path.levels.clock.op (m+1) p).push (R.family.path.rep N p (m+2)).beta (old.numerator hG)=b.density ∧ b.origins=(R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ old.roots ∧
        b.units=0 ∧ b.Active ∧ Seed.RadialReceipt b τ prev ∧ ∃fee : ℝ, WilsonRootedTwoDateOldInvoice.Paid old hG b τ fee ∧ fee≤phase old hG*(cash+cash) := by
  obtain ⟨first,price⟩ := Filter.eventually_atTop.1 (WilsonRootedOPEPointPrice.purchased R u hG)
  filter_upwards [eventually_ge_atTop first] with m reached
  obtain ⟨cash,booked⟩ := price (m+2) (by omega)
  refine ⟨max cash 0,le_max_right _ _,?_⟩
  intro N p old roster prev one
  subst u
  let D := ActualOriginalQPointSetup.pointDatum R old.request p (m+2) old.roots
  let x := testInclusion (ActualOriginalQPointSetup.request R old.labels old.request).tests old.test
  let c := ActualOriginalQInitialInput.scales R hG old.labels old.request old.schedule old.datum old.prescription old.roots old.scale old.degree
  let o := (ActualOriginalQPackets.positions D old.labels).origin
  have same : o=old.roots := funext fun i=>ActualOriginalQPointDatum.root_eq R _ _ _ _ _ i
  let P := ActualRunSpring.selected R N p (m+1) old.below
  have stock : Menu.Arsenal (R.family.path.rep N p (m+2)) := Mallow.Many.sharp (A:=R.alloy) (m:=m+1) (n:=p) (Q:=fun _=>(R.family.path.rep N p (m+2))) P.point (RunPhysicalMarks.actual_hasSlots R N p (m+2) old.below)
  obtain ⟨family,all⟩ := booked N p old.below old.roots (fun i=>(old.request.tests i).D) (fun _=>0) old.prescription (old.scale-R.family.S.scale N) old.degree stock
  let X := VariableScaling.tests c x
  obtain ⟨read,offered⟩ := all X
  let q := family X
  let fee := sitePrice q
  have trueOffer : Menu.Offer o q (oneW) (R.family.path.rep N p (m+2)).p.B ((R.family.path.rep N p (m+2)).p.supportExponent-4) fee :=
    ⟨offered.sites,QLocalPhysicalBirthMenu.hit _ _ _ _ (fun _=>Menu.Crew (oneW) (fun _=>zero_lt_one))⟩
  have cost0 : 0≤fee := Push.AbsoluteSums.budget_nonneg (trueOffer.budget 0)
  let τ := QLocalFullRootedOffer.radius 1 fee
  obtain ⟨pos,leone,limited⟩ := QLocalFullRootedOffer.limited o (oneW) (fun _=>zero_lt_one) q 1 zero_lt_one ((R.family.path.rep N p (m+2)).p.supportExponent-4) (R.family.path.rep N p (m+2)).p.B trueOffer
  have reserve := (ManuscriptQLocalMarkedGradeTail.campaign R spring).2 0
  have occurs : Extra.Multi.Occupancy ((R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ o) (R.family.path.levels.clock.J (m+2)) := by
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
  have deposit : (R.family.path.levels.clock.op (m+1) p).push (R.family.path.rep N p (m+2)).beta (old.numerator hG)=b.density := hn.symm ▸ pushed
  refine ⟨τ,pos,leone,b,deposit,roots.trans (congrArg ((R.family.path.levels.clock.op (m+1) p).ratio.parent ∘ ·) same),shares.units.1,live,paid,fee,⟨?_,cost0,inverse⟩,?_⟩
  · refine ⟨q,hn,deposit,?_,rfl,?_⟩
    · exact same ▸ trueOffer
    · intro other alt
      exact QLocalPhysicalBirthMenu.least _ _ _ _ alt.budget
  · have nonneg : 0≤phase old hG := by unfold phase WilsonRootedOPEPhase.wallet; positivity
    exact (QLocalPhysicalBirthMenu.least _ _ _ _ offered.budget).trans (mul_le_mul_of_nonneg_left (add_le_add (le_max_left cash 0) (le_max_left cash 0)) nonneg)


end YM.Integration.WilsonRootedTwoDateOldPointInvoice
