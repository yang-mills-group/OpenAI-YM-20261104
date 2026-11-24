import YM.Integration.WilsonOriginalOPECompleteExpense
import YM.Integration.WilsonRootedPhysicalUsable
import YM.Integration.WilsonRootedPhysicalSpringElection

/-! The original tested OPE is deposited on the native spring, including the
complete ordinary exponential and its forced Nat-indexed gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalOPEDeposit
open Function Finset Lattice Wilson RG Source Labels Marker FVA1
open MergeProof MergeProof.Accent PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Daisy.Charity.RG12 LocalComparison ComparisonDensity.Address
open RG3.Held RG3.Script.Picnic OriginalForcedAddresses ActualOriginalQReaders
open Push Push.PriceCompiler Extra.Trajectories Push.GridApprox.Nil
open FullQLocal FullQLocal.RenderedStep PhysicalNext.JointLoad UVNext.CouplingReset
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {N period m : ℕ} {below : m<N}
    (P : ActualRunSpring.Packet R N period m below) {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G}
    {V I : Type} [DecidableEq V] [Fintype V] [Fintype I] (Γ : Census V)
local notation "sourceRep" => P.input P.point.val
local notation "house₀" => Mallow.houseS P.spring P.point
local notation "step" => R.alloy.B.a.clock.op m period
local notation "coarse" => P.spring.result P.point.val
local notation "beta" => R.alloy.B.a.clock.hatBeta (m+1)
local notation "coupon" => Push.SectorMeasure.Chi.canonical

/-- This account records the incoming expense at the caller's radius, the paid
radius on the original photographed pupil, the complete deposit, and its recovery. -/
def Account (o : V→Site (R.family.side (m+1) period)) (w : V→ℝ)
    (source : Config G (R.family.side (m+1) period)→Poly Γ) (rows : I→Menu.Hat Γ (sourceRep)) : Prop :=
  source=GapsLocal.Full.given rows 0 ∧ source=Menu.Expense (Menu.heap rows) w (step) ∧
  ∃ D : ℝ, Menu.Offer o rows w (sourceRep).p.B ((sourceRep).p.supportExponent-4) D ∧
    let whole := Menu.heap rows
    let δ := QLocalFullRootedOffer.radius (Mallow.station (beta)) (D+Real.exp D*D)
    let r := fun v => δ*w v
    let M := fun i => (whole i).M
    let cash := fun i => Menu.sumFee (whole i) r
    let K := Mallow.Many.pupilK P.spring P.point M cash
    0<δ ∧ δ≤1 ∧ (∃ income volume decay : ℝ, Merge.Photo.Usable M (house₀) (coupon) (coarse) cash K income volume decay) ∧
    ManuscriptQLocalIntegratedTicket.Deposited (house₀) (coupon) whole r (coarse) K ∧
    ManuscriptQLocalIntegratedTicket.Recovered (house₀) (coupon) whole w r (coarse) K

private theorem receive (hG : G.Simple) (paid : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (o : V→Site (R.family.side (m+1) period)) (w : V→ℝ) (hw : ∀i,0<w i)
    (occ : Extra.Multi.Occupancy ((step).ratio.parent ∘ o) (R.alloy.B.a.clock.J (m+1)+1))
    (a : I→Menu.Hat Γ (R.family.path.rep N period (m+1))) {D : ℝ}
    (offer : Menu.Offer o a w (R.family.path.rep N period (m+1)).p.B
      ((R.family.path.rep N period (m+1)).p.supportExponent-4) D) :
    ∃ rows : I→Menu.Hat Γ (sourceRep), Account R P Γ o w (GapsLocal.Full.given a 0) rows := by
  obtain ⟨rows, same, ticket⟩ := WilsonOriginalOPECompleteExpense.transported a P.fine o w offer
  have rep := (P.spring.knows P.point.val P.point.property).1
  obtain ⟨_,bounds⟩ := ManuscriptQLocalMarkedGradeTail.campaign R paid
  have exponent : 100≤(sourceRep).p.supportExponent := rep.point.symm ▸ bounds (m+1)
  have de : 0≤(sourceRep).p.supportExponent-4 := by linarith
  have complete := Menu.counts rows w o (sourceRep).p.B hw ticket de
  have hb : 0<Mallow.station (beta) := Real.rpow_pos_of_pos (zero_lt_one.trans (R.alloy.B.a.fits.delayed (m+1))) _
  obtain ⟨pos,top,bought⟩ := QLocalFullRootedOffer.limited o w hw (Menu.heap rows) (Mallow.station (beta)) hb
    ((sourceRep).p.supportExponent-4) (sourceRep).p.B complete
  let τ := QLocalFullRootedOffer.radius (Mallow.station (beta)) (D+Real.exp D*D)
  have hr (i : V) : 0< τ*w i := mul_pos pos (hw i)
  exact ⟨rows, same, same.trans (WilsonOriginalOPECompleteExpense.spent rows (step) w hw rep.valid),
    D,ticket,pos,top, WilsonRootedPhysicalUsable.physical R P hG paid Γ (Menu.heap rows) o _ hr occ bought,
    ManuscriptQLocalSpringTicket.original R P hG paid Γ (Menu.heap rows) o _ hr occ bought,
    ManuscriptQLocalSpringTicket.restored R P hG paid Γ (Menu.heap rows) o w _ hw hr occ bought⟩

variable {B : MS.Local.Physical.Deck G} {n : ℕ} {hn : n ≤ m + 1} [Nonempty V]
    (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R period (m+1) n hn V)
    (u : V→MS.Rake.Label B) (μ : ℝ) (orders : V→ℕ)

/-- The incoming physical source is purchased directly from its original signed
point pages. Every choice of tests is read against the same original spring. -/
theorem physical (hG : G.Simple) (paid : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (href : ∀s : Slot u,R.family.ref s.2.size ≤ m + 1)
    (occ : Fintype.card V≤R.alloy.B.a.clock.J (m+1)+1)
    (w : V→ℝ) (hw : ∀i,0<w i) (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) :
    ∃ rows : Bool × ActualRunFullPages.Index (ActualOriginalQInput.atomPositions D u) →
      Menu.Hat (Stock.census V) (sourceRep), Account R P (Stock.census V) (ActualOriginalQPackets.positions D u).origin w
      ((ActualOriginalQInput.input Q D u μ orders hG N below).leaf x).density rows := by
  let o := (ActualOriginalQPackets.positions D u).origin
  have stock : Menu.Arsenal (R.family.path.rep N period (m+1)) :=
    Mallow.Many.sharp (A:=R.alloy) (m:=m) (n:=period) (Q:=fun _=> R.family.path.rep N period (m+1))
      P.point (RunPhysicalMarks.actual_hasSlots R N period (m+1) below)
  obtain ⟨family,all⟩ := WilsonOriginalOPEPageMenu.realized Q D u μ orders hG N below href stock w hw
  obtain ⟨source,C,offer⟩ := all x
  have occupancy : Extra.Multi.Occupancy ((step).ratio.parent ∘ o) (R.alloy.B.a.clock.J (m+1)+1) :=
    fun _ => (Finset.card_le_univ _).trans occ
  rw [source]
  exact receive R P (Stock.census V) hG paid o w hw occupancy (family x) offer

end YM.Integration.WilsonRootedPhysicalOPEDeposit
end
