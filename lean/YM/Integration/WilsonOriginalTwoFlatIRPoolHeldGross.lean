import YM.Integration.WilsonOriginalObservedRoseVanePurse
import YM.Integration.WilsonOriginalTwoFlatIRPoolBook
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRPoolHeldGross
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


open WilsonOriginalTwoFlatIRPoolBook (Tested)
open WilsonPositionThermometerConnected (value)
open WilsonOriginalObservedRoseMeshHeight (height)
open WilsonOriginalObservedRoseVanePurse (ages)
local notation "Faces" => Finset (Fin 3)

/-- The original cofactors at the fixed u are bought before the trial depth
and the width of the subsequent infrared transport. -/
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(hl:(l:Filter _)≤order.fuse)
    {u T h:ℕ}{δ:ℝ}(books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z 6 T s.val)
    (x:∀i:Fin 3,RG17.Free C (grade i).val)(φ:Test 3)(purchase:Tested F Jr Z (h:=h) books u x φ):
    ∃e:ℕ,∃C₀:ℝ,1≤C₀ ∧ ∀ᶠr in trail,∀ρ:Fin 3→{s:ℝ //0<s ∧ s<δ},
    (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∃uf:u≤f,∀ᶠp:ℕ×ℕ in (l:Filter _),∀K:ℕ,∀fk:f≤K,∀kn:K≤p.1,
    ∀o:cells R φ r (f,p.2),∀(Y:(i:Fin 3)→(C).label (grade i).val)(turn:Fin 3→Motion),
      (∀i,displayed R (grade i).val (Y i) (turn i)=(home F Jr Z (books (ρ i)) (grade i) (x i)).arm.source p) →
    ∀s:Faces,s.Nonempty →
    let price:=C₀*((wilson z r)⁻¹)^e
    let topValue:=incumbent R (N:=p.1) Y turn o.val s
    let b:=held R kn (uf.trans fk) Y turn o.val s
    ‖topValue‖≤price ∧ ‖b‖≤price ∧ r^(height ages s)*‖b‖≤price:=by
  obtain ⟨e,B,bp,initial,catalogue⟩:=purchase
  obtain ⟨A,an,raw⟩:=catalogue 0
  refine ⟨e,B+A,by linarith,?_⟩
  have clock:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have rp:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  have small:∀ᶠr:ℝ in trail,r<1:=(gt_mem_nhds (by norm_num:(0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [initial,raw,clock.positive,(clock.conforms simple).eventually (ge_mem_nhds zero_lt_one),rp,small]
    with r wage channel gp low pos little
  intro ρ span near f
  obtain ⟨uf,atEar⟩:=channel.1 ρ span near
  refine ⟨uf,?_⟩
  filter_upwards [wage ρ span near,(large_mesh order (f+1)).filter_mono hl] with np gross live
  intro K fk kn o Y turn names s hs price topValue b
  let g:=wilson z r
  have kg:1≤g⁻¹:=(one_le_inv₀ gp).mpr low
  have k:1≤(g⁻¹)^e:=one_le_pow₀ kg
  have ab:=atEar np.1 np.2 live o Y turn names s hs K fk kn
  have ab':‖topValue-b‖≤A:=ab.trans ((mul_le_mul_of_nonneg_left (pow_le_one₀ gp.le low) an).trans_eq (mul_one A))
  have born:=gross (show f<np.1 from live).le o Y turn names s
  have extra:A≤A*(g⁻¹)^e:=by simpa using mul_le_mul_of_nonneg_left k an
  have below:‖b‖≤price:=by
    calc ‖b‖ ≤ ‖b-topValue‖+‖topValue‖:=norm_le_norm_sub_add _ _
         _ = ‖topValue-b‖+‖topValue‖:=by rw [norm_sub_rev]
         _ ≤ A+B*(g⁻¹)^e:=add_le_add ab' born
         _ ≤ price:=by dsimp [price];rw [add_mul];linarith
  exact ⟨born.trans (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans k)),below,
    (mul_le_mul_of_nonneg_right (pow_le_one₀ pos.le little.le) (norm_nonneg b)).trans ((one_mul _).le.trans below)⟩

end YM.Integration.WilsonOriginalTwoFlatIRPoolHeldGross
end
