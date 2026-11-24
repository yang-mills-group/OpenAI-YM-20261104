import YM.Integration.WilsonRootedFirstInteriorCarry

/-! The inherited OPE and a subsequent authentic OPE are registered together on the
physical spring's photographed pupil. The native barcode field is kept literally. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedTwoDateMenu
open Filter Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence ActualOriginalQReaders Extra.Trajectories
open private receive from YM.Integration.WilsonRootedPhysicalOPEDeposit
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) {m N p : ℕ}
local notation "Γ₀" => Stock.census V
local notation "lowerRep" => R.family.path.rep N p (m+1)
local notation "lowerStep" => R.family.path.levels.clock.op m p
local notation "upperStep" => R.family.path.levels.clock.op (m+1) p

omit [Nonempty V] in
/-- The two independent physical tests enter the regular exponent and the same
exceptional barcode field. The latter contains both signed rows before `field`. -/
theorem together {Γ : Census V} {f : Side} {Y : RG.Rep G f} {I K : Type} [Fintype I] [Fintype K]
    (a : I→Menu.Hat Γ Y) (b : K→Menu.Hat Γ Y) (U : Config G f) :
    GapsLocal.Full.given (Sum.elim a b) 0 U = (Real.exp (Y.exponent U) : ℂ) •
      (Poly.pass ((∑i,Menu.odour (a i) U)+(∑j,Menu.odour (b j) U)) *
        Accent.field (fun c=> (Accent.bar Y.activities Γ U c+∑i,Menu.fragrance (a i) U c)+
          ∑j, Menu.fragrance (b j) U c) (RG.flags Y.p.threshold U)) := by
  have zero : Accent.Mach Γ 0=0 := by simp [Accent.Mach,Poly.send_zero]
  simp only [GapsLocal.Full.given,zero,Extra.Trajectories.pass_zero,one_mul,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,add_assoc]

variable (b : Overlay.Bands (Γ₀) (lowerRep)) (w : V→ℝ) (prev : ℕ) (below : m<N)
    (J : Request V) (u : V→MS.Rake.Label B) (Q : MS.Land.Prescription B) (μ : ℝ) (orders : V→ℕ) (hG : G.Simple)
local notation "C₀" => OriginalMarkedBandSuccessor.ceiling R m (Fintype.card V) prev
local notation "r₀" => fun v=>QLocalFullRootedOffer.radius 1 (C₀)*w v
local notation "P₀" => ActualRunSpring.selected R N p m below
local notation "D₀" => ActualOriginalQPointSetup.pointDatum R J p (m+1) b.origins
local notation "freshIndex" => Bool × ActualRunFullPages.Index (ActualOriginalQInput.atomPositions (D₀) u)
local notation "freshSource" => ActualOriginalQInput.input Q (D₀) u μ orders hG N below

/-- The two finite paid row families are read on the same photographic pupil. -/
def Combined {I K : Type} [Fintype I] [Fintype K] (P : ActualRunSpring.Packet R N p m below)
    (o : V→Site (R.family.side (m+1) p)) (r : V→ℝ)
    (a : I→Menu.Hat (Γ₀) (lowerRep)) (f : K→Menu.Hat (Γ₀) (lowerRep)) : Prop :=
  ∃ fee : ℝ, Menu.Offer o f r (lowerRep).p.B ((lowerRep).p.supportExponent-4) fee ∧
    Menu.Offer o (Sum.elim a f) r (lowerRep).p.B ((lowerRep).p.supportExponent-4) (1+fee) ∧
    ∃ rows : I ⊕ K → Menu.Hat (Γ₀) (P.input P.point.val),
      WilsonRootedPhysicalOPEDeposit.Account R P (Γ₀) o r (GapsLocal.Full.given (Sum.elim a f) 0) rows

/-- The fresh genuine OPE and the full joint account for one issued lower band menu. -/
def Installed {I K X : Type} [Fintype I] [Fintype K] (P : ActualRunSpring.Packet R N p m below)
    (o : V→Site (R.family.side (m+1) p)) (r : V→ℝ) (old : I→Menu.Hat (Γ₀) (lowerRep))
    (source : X → Config G (R.family.side (m+1) p) → Poly (Γ₀)) : Prop :=
  ∃ fresh : X → K → Menu.Hat (Γ₀) (lowerRep), ∀ x,
    source x=GapsLocal.Full.given (fresh x) 0 ∧ Combined R below P o r old (fresh x)

theorem register {I : Type} [Fintype I] {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G}
    (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T) (P : ActualRunSpring.Packet R N p m below)
    {n : ℕ} {hn : n ≤ m+1} (D : ActualRunQlocalNativeTuple.Datum R p (m+1) n hn V)
    (o : V→Site (R.family.side (m+1) p)) (same : (ActualOriginalQPackets.positions D u).origin=o)
    (a : I→Menu.Hat (Stock.census V) (R.family.path.rep N p (m+1)))
    (r : V→ℝ) (hr : ∀v,0<r v)
    (entered : Menu.Offer o a r (R.family.path.rep N p (m+1)).p.B ((R.family.path.rep N p (m+1)).p.supportExponent-4) 1)
    (sites : ∀s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ m+1) (room : Fintype.card V ≤ R.alloy.B.a.clock.J (m+1)) :
    Installed R below (K:=Bool × ActualRunFullPages.Index (ActualOriginalQInput.atomPositions D u)) P o r a
      (fun x=>((ActualOriginalQInput.input Q D u μ orders hG N below).leaf x).density) := by
  have stock : Menu.Arsenal (R.family.path.rep N p (m+1)) := Mallow.Many.sharp (A:=R.alloy) (m:=m) (n:=p)
    (Q:=fun _=> R.family.path.rep N p (m+1)) P.point (RunPhysicalMarks.actual_hasSlots R N p (m+1) below)
  obtain ⟨family,all⟩ := WilsonOriginalOPEPageMenu.realized Q D u μ orders hG N below sites stock r hr
  refine ⟨family,?_⟩
  intro x
  obtain ⟨leaf,fee,offer⟩ := all x
  have atRoot := (congrArg (fun v=>Menu.Offer v (family x) r (lowerRep).p.B ((lowerRep).p.supportExponent-4) fee) same).mp offer
  have summed := entered.cross atRoot
  have occ : Extra.Multi.Occupancy ((lowerStep).ratio.parent ∘ o) (R.alloy.B.a.clock.J (m+1)+1) :=
    fun _ => (Finset.card_le_univ _).trans (room.trans (Nat.le_succ _))
  exact ⟨leaf,fee,atRoot,summed,receive R P (Stock.census V) hG spring o r hr occ (Sum.elim a (family x)) summed⟩

end YM.Integration.WilsonRootedTwoDateMenu
