import YM.Integration.WilsonReflectedMixedSubmittedSum
set_option warningAsError true
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonReflectedMixedSubmittedHearing
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
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory WilsonMeasuredPublicEntranceHeadBoard
open WilsonAddressedAlignedColumn WilsonReflectedPublicStationFare
open WilsonThermometerOffsetCylinder WilsonThermometerOffsetTrajectory


open WilsonReflectedMixedMasterAxes (Fixed)
open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)

open WilsonReflectedMixedMasterRegistry (Gallery Delivery)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)


open WilsonThermometerUnitFilingFourSquare
open WilsonPositionHomogeneousFrame
open MS MS.Land FVA2 FVA2.Register

variable {d:ℕ}


abbrev Port (u:S.Field d):=WilsonThermometerUnitFilingFourSquare.Arm C S (l:Filter _) d u

def viewed (turn:Option Signed)(v:S.Field d):S.Field d:=match turn with
  | none=>v
  | some s=>S.mirror F.room.kernel.spin d s (S.conj F.room.kernel.spin d v)

def placed (turn:Option Signed)(Y:(C).label d):(C).label d:=match turn with
  | none=>Y
  | some s=>(C).book.mirrorGroup d s (star Y)

def oriented (turn:Option Signed){v:S.Field d}(A:Port (R:=R) (l:=l) v):Port (R:=R) (l:=l) (viewed F turn v):=
  match turn with
  | none=>A
  | some s=>WilsonThermometerUnitFilingFourSquare.reflected F A s

theorem source (turn:Option Signed){v:S.Field d}(A:Port (R:=R) (l:=l) v)(y:ℕ×ℕ):
    (oriented F turn A).source y=placed (R:=R) turn (A.source y):=by cases turn <;>rfl

/-- The original finite rows may use convergent measured scalars at the
cutoffs. All their ordinary, uncentered moments then hear the nominated sum. -/
def audition {ι:Type}[Fintype ι](J:ℝ→tower S)(Z:WilsonPrescription G)(r:ℝ)(x:ι→RG17.Free C d)
    (c:ι→ℂ)(w:ι→(ℕ×ℕ)→ℂ)(limits:∀i,Tendsto (w i) (l:Filter _) (𝓝 (c i)))
    (rows:∀i,Port (R:=R) (l:=l) (homogeneous F J Z r d (x i))):
    Port (R:=R) (l:=l) (homogeneous F J Z r d (∑i,c i•x i)) where
  source a:=∑i,w i a•(rows i).source a
  label:=∑i,c i•(rows i).label
  approaches:=tendsto_finsetSum Finset.univ (fun i _=>(limits i).smul (rows i).approaches)
  represents:=by simp only [map_sum,map_smul,(rows _).represents]

/-- Repeated basis labels, both measured presentations and the reflected
slots use one original joint cutoff numerator and the same physical extraction. -/
theorem original {Λ:Type}{n:ℕ}(J:ℝ→tower S)(Z:WilsonPrescription G)(live:(l:Filter _)≤order.fuse)
    (d q:Λ→ℕ)(r:Λ→ℝ)(x:(b:Λ)→Fin (q b)→RG17.Free C (d b))
    (c:(b:Λ)→Fin (q b)→ℂ)(w:(b:Λ)→Fin (q b)→(ℕ×ℕ)→ℂ)
    (limits:∀b i,Tendsto (w b i) (l:Filter _) (𝓝 (c b i)))
    (rows:∀b, Bool→∀i,Port (R:=R) (l:=l) (homogeneous F J Z (r b) (d b) (x b i)))
    (labels:Fin n→Λ)(choose:Fin n→Bool)(turns:Fin n→Option Signed)(t:Test n):
    Tendsto (fun z:ℕ×ℕ=>Order.smears C z.1 z.2
      (fun a=>⟨d (labels a),placed (R:=R) (turns a)
        (∑i,w (labels a) i z•(rows (labels a) (choose a) i).source z)⟩) t) (l:Filter _)
      (𝓝 (t.applyTo (fun p=>S.classMoment S (d∘labels) p
        (fun a=>viewed F (turns a) (homogeneous F J Z (r (labels a)) (d (labels a))
          (∑i,c (labels a) i•x (labels a) i)))))):=by
  let V:=fun a:Fin n=>viewed F (turns a) (homogeneous F J Z (r (labels a)) (d (labels a))
    (∑i,c (labels a) i•x (labels a) i))
  let A:(a:Fin n)→Bool→Port (R:=R) (l:=l) (V a):=fun a b=>oriented F (turns a)
    (audition F J Z _ (x (labels a)) (c (labels a)) (w (labels a)) (limits (labels a)) (rows (labels a) b))
  have paid:=WilsonThermometerUnitFilingFourSquare.measured (d:=d∘labels) (v:=V) F live A choose t
  apply paid.congr' (Filter.Eventually.of_forall ?_)
  intro z
  apply congrArg (fun q:Fin n→(C).book.Token=>Order.smears C z.1 z.2 q t)
  funext a
  apply congrArg (fun q:(C).label (d (labels a))=>(⟨d (labels a),q⟩:(C).book.Token))
  exact source F (turns a) _ z

end YM.Integration.WilsonReflectedMixedSubmittedHearing
end
