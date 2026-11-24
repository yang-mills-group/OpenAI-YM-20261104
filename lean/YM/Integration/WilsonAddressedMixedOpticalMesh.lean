import YM.Integration.WilsonAddressedMixedThermalClock
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedMixedOpticalMesh
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


omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h t:ℕ)(deep:2 ≤ t)(d:I → Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z D T s.val):
    ∃A:ℝ,1 ≤ A ∧ ∀ᶠr in trail,∀ρ:I → {s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) → 
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      let K:=berth R t f
      0<wilson z r ∧ a K/a f ≤ wilson z r ∧ (β K)*(wilson z r)^2 ≤ A:=by
  classical
  obtain ⟨A,ap,closed⟩:=WilsonAddressedMixedThermalClock.original F simple bliss slow D T h t d books
  refine ⟨A,ap,?_⟩
  filter_upwards [closed,WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books,
    WilsonOriginalTwoFlatPublicOuter.original F simple bliss 1,
    (wilson_link F simple bliss.budgets bliss.keen bliss.lies).positive] with r earned hired outerRoom gp
  intro ρ span near m f K
  refine ⟨gp,?_,earned ρ span near⟩
  have inverse:(wilson z r)⁻¹ ≤ (β f)^2:=by
    apply (mul_le_mul_iff_of_pos_left outerRoom.1).mp
    simpa only [outer,pow_one,Nat.mul_one,mul_comm ((β f)^2) r] using outerRoom.2.2 f (hired ρ span near).1
  have grown:(β f)^2 ≤ (β f)^t:=pow_le_pow_right₀ ((P).fits.delayed f).le deep
  have bill:=((mul_le_mul_of_nonneg_left (inverse.trans grown) ((C).S.a_pos K).le).trans
    (WilsonInvariantActionPosition.arrival R t f).2)
  rw [div_le_iff₀ ((C).S.a_pos f)]
  rw [←div_eq_mul_inv,div_le_iff₀ gp] at bill
  exact bill.trans_eq (mul_comm ..)

end YM.Integration.WilsonAddressedMixedOpticalMesh
end
