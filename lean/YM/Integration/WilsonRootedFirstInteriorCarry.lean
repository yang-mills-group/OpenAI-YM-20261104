import YM.Integration.WilsonRootedPhysicalOPEDeposit
import YM.Integration.OriginalMarkedBandSuccessor

/-! The actual tested OPE crosses the first step as a full signed nonlinear band.
The same band buys a native menu at the first interior date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedFirstInteriorCarry
open Filter Function Finset Lattice Wilson RG Source Labels Marker FVA1
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open PhysicalNext.Repeat.Daisy MergeProof Org GapsLocal.Renew
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonOriginalMarkedExistence
open scoped Classical BigOperators Topology
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    {B : MS.Local.Physical.Deck G} (R : Run G) {m N p : ℕ}
local notation "Γ₀" => Stock.census V
local notation "topRep" => R.family.path.rep N p (m+2)
local notation "lowerRep" => R.family.path.rep N p (m+1)
local notation "upperStep" => R.family.path.levels.clock.op (m+1) p

/-- The lower density, its sites, signed active rows and its next paid width refer
to a single band, before any new lower-field insertion. -/
def Inherited (o : V→Site (R.family.side (m+2) p)) (w : V→ℝ) (prev now : ℕ)
    (source : Config G (R.family.side (m+2) p)→Poly (Γ₀)) : Prop :=
  ∃ τ : ℝ, 0<τ ∧ τ ≤ 1 ∧ ∃ b : Overlay.Bands (Γ₀) (lowerRep),
    (upperStep).push (topRep).beta source=b.density ∧ b.origins=(upperStep).ratio.parent ∘ o ∧
    b.units=0 ∧ b.Active ∧ OriginalMarkedBandSuccessor.Booked R b (fun v=>τ*w v) prev now

omit [DecidableEq V] [Nonempty V] in
/-- A fixed degree and fixed genuine label set reach both consecutive native orders. -/
theorem eventually_ready (prev now : ℕ) (u : V→MS.Rake.Label B) :
    ∀ᶠ m : ℕ in atTop,
      GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2) ∧
      GapsLocal.Full.target 0 (Fintype.card V) now ≤ R.alloy.B.a.clock.J (m+1) ∧
      Fintype.card V ≤ R.alloy.B.a.clock.J (m+1) ∧ ∀s : ActualOriginalQReaders.Slot u,R.family.ref s.2.size ≤ m+1 := by
  let cap := max (GapsLocal.Full.target 0 (Fintype.card V) prev) (max (GapsLocal.Full.target 0 (Fintype.card V) now) (Fintype.card V))
  filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop cap,
    eventually_ge_atTop (ActualOriginalQLayout.referenceLevel R u)] with m large ref
  have room : cap ≤ R.alloy.B.a.clock.J (m+1) := large.trans (R.alloy.B.a.fits.mono (Nat.le_succ m))
  refine ⟨((le_max_left _ _).trans room).trans (R.alloy.B.a.fits.mono (Nat.le_succ (m+1))),
    ((le_max_left _ _).trans (le_max_right _ _)).trans room,
    ((le_max_right _ _).trans (le_max_right _ _)).trans room, ?_⟩
  exact ActualOriginalQLayout.reference_le R u (ref.trans (Nat.le_succ m))

/-- No signed particle has been dropped from the fine complete OPE or from its coarse band. -/
theorem original {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G} (hG : G.Simple)
    (spring : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (marks : Mallow.RG12.Earned (markerBudget G) R.kit.shape R.alloy.delay) (old : m+1<N)
    (prev now : ℕ)
    (first : GapsLocal.Full.target 0 (Fintype.card V) prev ≤ R.alloy.B.a.clock.J (m+2))
    (second : GapsLocal.Full.target 0 (Fintype.card V) now ≤ R.alloy.B.a.clock.J (m+1))
    {n : ℕ} {hn : n ≤ m+2} (D : ActualRunQlocalNativeTuple.Datum R p (m+2) n hn V)
    (Q : MS.Land.Prescription B) (u : V→MS.Rake.Label B) (μ : ℝ) (orders : V→ℕ)
    (sites : ∀s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ m+2) (w : V→ℝ) (hw : ∀v,0<w v)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) :
    Inherited R (N:=N) (ActualOriginalQPackets.positions D u).origin w prev now
      ((ActualOriginalQInput.input Q D u μ orders hG N old).leaf x).density := by
  let P := ActualRunSpring.selected R N p (m+1) old
  have stock : Menu.Arsenal (topRep) :=
    Mallow.Many.sharp (A:=R.alloy) (m:=m+1) (n:=p) (Q:=fun _=> (topRep))
      P.point (RunPhysicalMarks.actual_hasSlots R N p (m+2) old)
  obtain ⟨family,all⟩ := WilsonOriginalOPEPageMenu.realized Q D u μ orders hG N old sites stock w hw
  obtain ⟨read,fee,offer⟩ := all x
  let o := (ActualOriginalQPackets.positions D u).origin
  obtain ⟨pos,one,limited⟩ := QLocalFullRootedOffer.limited o w hw (family x) 1 zero_lt_one
    ((topRep).p.supportExponent-4) (topRep).p.B offer
  let τ := QLocalFullRootedOffer.radius 1 fee
  have reserve := (ManuscriptQLocalMarkedGradeTail.campaign R spring).2 0
  obtain ⟨b,pushed,origin,units,active,booked⟩ := OriginalMarkedBandSuccessor.twice R hG old marks reserve prev now
    first second o (fun v=>τ*w v) (fun v=>mul_pos pos (hw v)) (family x) limited
  exact ⟨τ,pos,one,b,read.symm ▸ pushed,origin,units,active,booked⟩

end YM.Integration.WilsonRootedFirstInteriorCarry
