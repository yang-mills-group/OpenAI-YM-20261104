import YM.Integration.WilsonOriginalTwoFlatIRPoolProper
import YM.Integration.WilsonOriginalTwoFlatIRPoolGain
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolBook
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

local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ → tower S)(Z:WilsonPrescription G)

open WilsonPositionThermometerGradedSource
local notation "heads" => source (C) (Finset.univ:Finset (Fin 3))
local notation "SiteSet" => {s:Finset (Fin 3)//s.Nonempty}

open WilsonPositionThermometerCapStation (Group)
open WilsonOriginalTwoFlatRoseNominated (face)
open WilsonOriginalTwoFlatRosePhase (fields)

open WilsonOriginalTwoFlatRoseBook (group)
open WilsonThermometerAlignedCells (atOrigin)
open WilsonOriginalTwoFlatRoseNominated (face)

open WilsonOriginalTwoFlatRoseRelativePhase (nodes recenter translated)

open WilsonMovingForkOpticalBook (reporter)
open WilsonOriginalTwoFlatIRSocketHeardCell (row incumbent held)
open WilsonOriginalTwoFlatIRPoolOrigins (home)
open WilsonReceivedChronologicalFixedRoseVariation (cells)

open WilsonPositionThermometerConnected (value)
open WilsonReceivedChronologicalFixedRoseVariation (signed)

def direct:Motion:=⟨1,false⟩

theorem target (d:ℕ)(Y:(C).label d):displayed R d Y direct=Y:=by
  simp [displayed,direct,show (1:Signed).ortho=1 from map_one Signed.inclusionO,Labels.Frame.act_one]

def Paid {T h q:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (u:ℕ)(x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(r bound:ℝ):Prop :=
  ∀ρ:Fin 3→{s:ℝ//0<s ∧ s<δ},(∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
  (∃i,(ρ i).val=r) → let f:=reporter F books ρ
  ∃uf:u ≤ f,∀ᶠp:ℕ×ℕ in (l:Filter _),∀K:ℕ,∀fk:f ≤ K,∀kn:K ≤ p.1,
    let nodes:=cells R φ r (f,p.2)
    ∀(Y:(o:nodes)→(i:Fin 3)→(C).label (grade i).val)(turn:nodes→Fin 3→Motion),
      (∀o i,displayed R (grade i).val (Y o i) (turn o i)=
        (home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source p) →
    ‖signed R φ r (f,p.2) (fun o=>value (incumbent R (N:=p.1) (Y o) (turn o) o.val)-
      value (held R kn (uf.trans fk) (Y o) (turn o) o.val))‖ ≤ (∫y,‖φ y‖)*(bound*(wilson z r)^q)

def Tested {T h:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (u:ℕ)(x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3):Prop :=
  ∃e:ℕ,∃B:ℝ,1 ≤ B ∧ (∀ᶠr in trail,WilsonOriginalTwoFlatIRPoolProper.Capped F Jr Z (h:=h) books x φ r (B*((wilson z r)⁻¹)^e)) ∧
    ∀q:ℕ,∃A:ℝ,0 ≤ A ∧ ∀ᶠr in trail,
      WilsonOriginalTwoFlatIRPoolChamber.Chamber F Jr Z (u:=u) (h:=h) (q:=q+2*e) books x φ r A ∧
      Paid F Jr Z (h:=h) (q:=q) books u x φ r (21*(B+A)^2*A)

/-- One signed finite Wilson experiment on the pooled arm of each actual department,
at the chosen before-cutoff stop and the same freely appointed family of books. -/
theorem on_book {J u:ℕ}(stop:Stop C 0 J u)(fac:Facilities C order S)(bliss:Bliss F l z H)
    (slow:WilsonWindowReportingPace.Slow R.kit)(lead:Leading F Jr)
    (owed:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)(hl:(l:Filter _) ≤ order.fuse)
    {T:ℕ}{δ:ℝ}(dp:0<δ)(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s))(h:ℕ)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3):Tested F Jr Z (h:=h) books u x φ:=by
  obtain ⟨e,B,bp,bound⟩:=WilsonOriginalTwoFlatIRPoolProper.original F Jr Z fac.simpleGate bliss slow lead owed hl books x φ h
  refine ⟨e,B,bp,bound,?_⟩
  intro q
  obtain ⟨A,an,earn⟩:=WilsonOriginalTwoFlatIRPoolChamber.original F Jr Z stop fac bliss slow lead owed dp books window x φ h (q+2*e)
  refine ⟨A,an,?_⟩
  have hg:=wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies
  filter_upwards [bound,earn,hg.positive,(hg.conforms fac.simpleGate).eventually (ge_mem_nhds zero_lt_one)] with r cap budget gp small
  refine ⟨budget,?_⟩
  intro ρ span near f
  obtain ⟨uf,visits⟩:=budget ρ span near
  refine ⟨uf,?_⟩
  filter_upwards [cap ρ span near,(large_mesh order (f+1)).filter_mono hl] with p upper live
  intro K fk kn nodes Y turn names
  have money:0 ≤ 21*(B+A)^2*A*(wilson z r)^q:=by positivity
  apply WilsonReceivedChronologicalFixedRoseVariation.original R φ r (f,p.2) _ _ money
  intro o
  exact WilsonOriginalTwoFlatIRPoolGain.seven _ _ gp small bp an q e
    (upper (show f<p.1 from live).le o (Y o) (turn o) (names o))
    (fun s hs=>visits p.1 p.2 live o (Y o) (turn o) (names o) s hs K fk kn)

/-- The original phase stop and books are selected before the reporting homes, fixed
public directions, profile and requested accuracy. -/
theorem original (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(owed:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (hl:(l:Filter _) ≤ order.fuse)(floor:ℕ):
    ∃J u:ℕ,floor ≤ J ∧ J ≤ u ∧ Stop C 0 J u ∧ ∃T:ℕ,∃δ:ℝ,0<δ ∧
      ∃books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val,
        (∀s,WilsonMovingForkWindowBooks.Priced F (books s)) ∧
        ∀(h:ℕ)(x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3),Tested F Jr Z (h:=h) books u x φ:=by
  obtain ⟨J,u,past,ready,stop⟩:=WilsonMovingForkElectedPhase.fixed (R:=R) fac floor
  obtain ⟨T,δ,dp,books,window⟩:=WilsonMovingForkWindowBooks.original F fac.simpleGate bliss 6
  exact ⟨J,u,past,ready,stop,T,δ,dp,books,window,on_book F Jr Z stop fac bliss slow lead owed hl dp books window⟩

end YM.Integration.WilsonOriginalTwoFlatIRPoolBook
end
