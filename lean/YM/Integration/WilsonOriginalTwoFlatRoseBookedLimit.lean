import YM.Integration.WilsonOriginalTwoFlatRoseBook
import YM.Integration.WilsonOriginalTwoFlatRoseObserved

/-! The unrestricted tested scalar of the chosen Vane at the elected physical
limit. The same booked lift supplies each marked local quotient on every cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatRoseBookedLimit
open Filter Finset Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits RG12 RG17 PhysMS PhysicalNext.Repeat.Legato WilsonThermometerUnitFilingFourSquare
open XSpace XSpace.Rose
open scoped Topology Classical BigOperators
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

open WilsonOriginalTwoFlatRoseObserved (observed)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonOriginalTwoFlatRoseFaceLimits (result)

theorem original (simple:G.Simple)(hl:(l:Filter _) ≤ order.fuse){T:ℕ}{δ:ℝ}
    (books:(r:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z 6 T r.val)
    (r:{s:ℝ // 0<s ∧ s<δ})(lift:Next.UVStress.Lifts C (books r).k)(φ:Test 3):
    let v(i:Fin 3):=homogeneous F Jr Z r.val (grade i) (heads i)
    Tendsto (observed R (group F Jr Z (books r) lift) r.val φ) (l:Filter _)
      (𝓝 (φ.applyTo (fun x=>WilsonPositionThermometerConnected.value (result R r.val v x)))):=by
  intro v
  let arms(i:Fin 3):= ((books r).rows (grade i)).arm true (v i)
  apply WilsonOriginalTwoFlatRoseObserved.original R F (group F Jr Z (books r) lift) simple hl r.val
    r.property.1 φ v arms
  intro p i
  exact WilsonOriginalTwoFlatRoseBook.same F Jr Z books r lift p.1 p.2 i

end YM.Integration.WilsonOriginalTwoFlatRoseBookedLimit
end
