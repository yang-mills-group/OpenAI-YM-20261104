import YM.Integration.OriginalMarkedCooledInvoice
import YM.Integration.WilsonRootedTwoDateRegularJoint
import YM.Integration.WilsonRootedTwoDateCoolingRows
import YM.Integration.WilsonRootedTwoDateMenu

/-! A genuinely cooled lower insertion has a finite ordinary native menu, and its entire
factor multiplies all of the signed incoming components at each configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateProduct.Seed
open Filter Function Finset MeasureTheory Lattice Wilson RG Marker Source Labels FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence
open private receive from YM.Integration.WilsonRootedPhysicalOPEDeposit
open scoped Classical Topology BigOperators
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} {R : Run G} {N p m : ℕ} (f : Seed R B V N p m) (hG : G.Simple)
local notation "Y" => R.family.path.rep N p (m+1)
local notation "Γ" => Stock.census V
local notation "ρ" => OriginalMarkedCooledInvoice.radius R hG f.labels f.request f.schedule m
local notation "K" => ↥(OriginalMarkedBirthRows.active R hG f.labels f.request f.schedule f.datum f.prescription f.roots f.scale f.degree) × Bool

omit [Nonempty V] in
theorem native_regular : 0<(ρ) ∧ (ρ)≤1 ∧ ∃ fresh : (K)→Menu.Hat (Γ) (Y),
    Menu.Offer f.roots fresh (fun _=>ρ) (Y).p.B ((Y).p.supportExponent-4) 1 ∧
    ∀{I : Type} [Fintype I] (old : I→Menu.Hat (Γ) (Y)) U,
      GapsLocal.Full.given (Sum.elim old fresh) 0 U=f.masked hG U*GapsLocal.Full.given old 0 U := by
  obtain ⟨pos,top,slot,fresh,keys,invoice,read⟩ := OriginalMarkedCooledInvoice.native R hG f.labels f.request f.schedule f.datum f.prescription f.roots f.scale f.degree f.test
  have root : (ActualOriginalQPackets.positions (ActualOriginalQPointSetup.pointDatum R f.request p (m+1) f.roots) f.labels).origin=f.roots := funext fun i=>ActualOriginalQPointDatum.root_eq R _ _ _ _ _ i
  have entered := (congrArg (fun roots=>Menu.Offer roots fresh (fun _=>ρ) (Y).p.B ((Y).p.supportExponent-4) 1) root).mp invoice
  refine ⟨pos,top,fresh,entered,?_⟩
  intro I inst old U
  have log (i : K) : (fresh i).M.turn=.logKey (slot i.1) := (keys i.1 i.2).2
  have reg (i : K) : Menu.odour (fresh i) U=Menu.amount (fresh i) U := by unfold Menu.odour MergeProof.prose; rw [log,Menu.varnish]
  have stock := OriginalMarkedOrdinaryDensity.original (Y) fresh (fun i=>slot i.1) (R.makes.wilson.represents N p (m+1) f.below).good.labels log U
  have hn : ((Y).eval U:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson f.below U).ne'
  have evaluated : GapsLocal.Full.given fresh 0 U=((Y).eval U:ℂ) • f.masked hG U := read U
  have fee : Poly.pass (∑i,Menu.amount (fresh i) U)=f.masked hG U := by
    have h := congrArg (fun z : Poly (Γ)=>((Y).eval U:ℂ)⁻¹ • z) (stock.symm.trans evaluated)
    simp only [smul_smul,inv_mul_cancel₀ hn,one_smul] at h
    exact h
  have same : (∑i,Menu.odour (fresh i) U)=∑i,Menu.amount (fresh i) U := Finset.sum_congr rfl (fun i _=>reg i)
  exact (WilsonRootedTwoDateMenu.regular old fresh (fun j=>⟨slot j.1,(keys j.1 j.2).2⟩) U).trans (congrArg (fun value=>value*GapsLocal.Full.given old 0 U) ((congrArg Poly.pass same).trans fee))

omit [Nonempty V] in
theorem native_joint {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G} (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (room : Fintype.card V≤ R.alloy.B.a.clock.J (m+1)) (P : ActualRunSpring.Packet R N p m f.below)
    {I : Type} [Fintype I] (old : I→Menu.Hat (Γ) (Y)) (s : ℝ) (hs : 0<s) (hs' : s≤1)
    (offer : Menu.Offer f.roots old (fun _=>s) (Y).p.B ((Y).p.supportExponent-4) 1) :
    0<s*(ρ) ∧ s*(ρ)≤1 ∧ ∃fresh : (K)→Menu.Hat (Γ) (Y),
      WilsonRootedTwoDateMenu.Combined R f.below P f.roots (fun _=>s*(ρ)) old fresh ∧
      ∀ U,GapsLocal.Full.given (Sum.elim old fresh) 0 U=f.masked hG U*GapsLocal.Full.given old 0 U := by
  obtain ⟨pos,top,fresh,new,field⟩ := f.native_regular hG
  have one := QLocalFullRootedOffer.scaled f.roots (fun _=>s) (fun _=>hs) old pos top ((Y).p.supportExponent-4) (Y).p.B offer
  have two := QLocalFullRootedOffer.scaled f.roots (fun _=>ρ) (fun _=>pos) fresh hs hs' ((Y).p.supportExponent-4) (Y).p.B new
  have oldOne : Menu.Offer f.roots old (fun _=>s*(ρ)) (Y).p.B ((Y).p.supportExponent-4) 1 := by
    simpa only [mul_comm (ρ) s] using one.fatten (show (ρ)*1≤1 by simpa using top)
  have freshOne := two.fatten (show s*1≤1 by simpa using hs')
  have sum := oldOne.cross freshOne
  have occ : Extra.Multi.Occupancy ((R.family.path.levels.clock.op m p).ratio.parent ∘ f.roots) (R.alloy.B.a.clock.J (m+1)+1) := fun _=>(Finset.card_le_univ _).trans (room.trans (Nat.le_succ _))
  exact ⟨mul_pos hs pos,(mul_le_mul_of_nonneg_left top hs.le).trans (by simpa using hs'),fresh,⟨1,freshOne,sum,receive R P (Γ) hG spring f.roots _ (fun _=>mul_pos hs pos) occ (Sum.elim old fresh) sum⟩,field old⟩

end YM.Integration.WilsonRootedTwoDateProduct.Seed
