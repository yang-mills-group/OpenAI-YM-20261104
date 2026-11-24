import YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedFitted
import YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedDeposit
import YM.Integration.WilsonMeasuredSignedActionDeposited
/-! The measured cone estimate on the publicly filed heterogeneous roster.
The observation uses the earlier Wilson vacuum at both real slices. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionPacket
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open WilsonOriginalPublicRelativeGramKineticMesh (thermal)

open RG.Supply Precision Next.Foundations WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace Extra.Histories Pert.Asymptotics
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramTrialPublicJointFourMixedFitted (field)
open WilsonPositionProgramTrialPublicJointFourMixedIncome (turned)
open WilsonPositionProgramTrialPublicJointFourSignedFitted (coefficient)
local notation "F₄" => R.family.labels.level 4


open WilsonMeasuredSignedActionDeposited (filled cleared)

/-- File the stock before taking either of the original regulator limits. -/
structure Packet {G:Gauge}(R:Run G){n:ℕ}(grade:Fin n→ℕ)(K:ℕ) where
  file:Filed R grade K
  words:(z:ℕ×ℕ)→∀j,R.family.label (grade j)
  turns:Fin n→Motion
  radius:ℝ
  gain:ℝ
  size_pos:0<radius
  gain_nonneg:0≤gain

namespace Packet
variable {n K:ℕ}{grade:Fin n→ℕ}
def vote (E:Packet R grade K)(z:ℕ×ℕ)(i:Fin n)(four:grade i=4):(F₄).Coeff:=
  turned R grade z.1 z.2 E.file (E.words z) E.turns i four

def measured {cap:ℕ}(fit:4<cap)(k:ℕ)(T₄:SectionData F₄)(E:Packet R grade K)(m:ℕ)
    (z:ℕ×ℕ)(i:Fin n)(four:grade i=4)(q:ℕ)(unit:ℂ):(F₄).Coeff:=
  filled F₄ (field R fit k T₄ m z.1 z.2 grade E.file (E.words z) E.turns E.radius E.gain i four q) unit

def scale (E:Packet R grade K)(m:ℕ)(z:ℕ×ℕ):ℝ:=
  coefficient R m K z.1 z.2 E.radius E.gain

theorem scale_nonneg (E:Packet R grade K)(m:ℕ)(z:ℕ×ℕ):0≤E.scale m z:=by
  unfold scale coefficient
  have := E.gain_nonneg
  exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg E.size_pos.le _)) this) (sq_nonneg _)

end Packet

def top {D T:ℕ}{δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (τ:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ}):ℕ:=
  berth R τ (berth R 5 (univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k))

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {base:ℕ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (D T h τ:ℕ)(deep:2*(2*(2*Γ.stage+2)+3)≤τ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    {cap k u e:ℕ}(fit:4<cap)(rails:Rails 4 k u e)(enough:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>cap) (fun _=>fit))≤k)
    (T₄:SectionData F₄){Hol₀:Hol G}(sound:T₄.Sound Hol₀)(pop:Bid.pop T₄):
    ∃M:ℝ,0≤M ∧ ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
    (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    ∀{n:ℕ}(grade:Fin n→ℕ)(E:Packet R grade (top F books τ ρ))(b:ℕ×ℕ),
    top F books τ ρ≤b.1→∀q:ℕ,2≤q→q≤e→∀(i:Fin n)(four:grade i=4)(unit:ℂ),
    let x:=(E.scale (Γ.date r) b:ℂ) • (F₄).core (E.vote b i four)
    (F₄).coeffSize (x-(F₄).core (E.measured fit k T₄ (Γ.date r) b i four q unit))
      ≤ M*(wilson z r)^(1/8:ℝ)*(F₄).coeffSize x:=by
  obtain ⟨M,pos,salary⟩:=WilsonPositionProgramTrialPublicJointFourBookedFitted.original F simple bliss slow Γ D T h τ
    deep d books v₀ funded fit rails enough capacity T₄ sound pop
  refine ⟨M,pos,salary.mono ?_⟩
  intro r paid ρ actual near n grade E b live q low high i four unit x
  let B:=field R fit k T₄ (Γ.date r) b.1 b.2 grade E.file (E.words b) E.turns E.radius E.gain i four q
  have amount:(F₄).coeffSize (B-x)≤M*(wilson z r)^(1/8:ℝ)*(F₄).coeffSize x:=
    paid ρ actual near b.1 b.2 live q low high grade E.file (E.words b) E.turns E.radius E.gain
      E.size_pos E.gain_nonneg i four
  change (F₄).coeffSize (x-(F₄).core (filled F₄ B unit))≤_
  have zero:B 0=0:=by
    have coreZero(v:(F₄).Coeff):(F₄).core v 0=0:=by simp [Frame.core]
    exact coreZero _
  rw [cleared F₄ B unit zero]
  have swap:(F₄).coeffSize (x-B)=(F₄).coeffSize (B-x):=Finset.sum_congr rfl (fun j _=>norm_sub_rev _ _)
  rwa [swap]

end YM.Integration.WilsonMeasuredSignedActionPacket
end
