import YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedFitted
import YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedDeposit

/-! The originally enrolled compact Wilson action in a heterogeneous source panel. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedReceipt
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

open WilsonReflectedFundedHearing (Arm)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open WilsonPositionProgramTrialPublicJointFourMixedDeposit (actual)

def Heard {cap:ℕ}(fit:4<cap)(k e m K:ℕ)(θ M:ℝ):Prop:=
  ∀N per:ℕ,K≤N → ∀q:ℕ,2≤q → q≤e → ∀{n:ℕ}(grade:Fin n→ℕ)(file:Filed R grade K)
  (Y:∀i,R.family.label (grade i))(turn:Fin n→Motion)(rr gain:ℝ),0 < rr → 0 ≤ gain →
  ∀(i:Fin n)(same:grade i=4){f:ℕ}(A:Arm R (grade i) N per f K),
    A.w=(file.A N per i).symm (fitted R (grade i) (file.station i) N per (Y i)) → (A.s,A.b)=turn i →
    let b:=actual R same fit k m N per (R.family.localSection 4) rr gain A q
    let w:=turned R grade N per file Y turn i same
    let x:=(coefficient R m K N per rr gain:ℂ) • (F₄).core w
    (F₄).coeffSize (b-x)≤M*θ^(1/8:ℝ)*(F₄).coeffSize x

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {base:ℕ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (D T h τ:ℕ)(deep:2*(2*(2*Γ.stage+2)+3) ≤ τ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    {cap k u e:ℕ}(fit:4<cap)(rails:Rails 4 k u e)(enough:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>cap) (fun _=>fit))≤k):
    ∃M:ℝ,0≤M ∧ ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let s₀:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 s₀
      Heard (R:=R) fit k e (Γ.date r) (berth R τ f) (wilson z r) M:=by
  obtain ⟨M,M₀,quote⟩:=WilsonPositionProgramTrialPublicJointFourBookedFitted.original F simple bliss slow
    Γ D T h τ deep d books v₀ funded fit rails enough capacity (R.family.localSection 4)
    (R.makes.sections 4) (FVAAlt2.Block.clothes R 4)
  refine ⟨M,M₀,?_⟩
  filter_upwards [quote] with r paid
  intro ρ chosen tied s₀ f N per top q floor depth n grade file Y turn rr gain rr₀ rate i same f₀ A placed oriented b w x
  have unit:=WilsonPositionProgramTrialPublicJointFourMixedDeposit.filed R grade i same fit k (Γ.date r) N per
    (R.family.localSection 4) file Y turn rr gain A placed oriented q
  change (F₄).coeffSize (actual R same fit k (Γ.date r) N per (R.family.localSection 4) rr gain A q-x)≤_
  rw [unit]
  exact paid ρ chosen tied N per top q floor depth grade file Y turn rr gain rr₀ rate i same

end YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedReceipt
end
