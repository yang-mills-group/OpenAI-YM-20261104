import YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan
/-! One public date works for all named detector radii in the physical
polynomial window, including a face omitting the arm that sets the date. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh
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

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ}, (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=berth R 5 m
      a j/r ≤ (wilson z r)^2 ∧ ∀i,(ρ i).val ≤ (β j)^(2*T+11+2*h)*a j:=by
  have bounds:=fun [Nonempty I]=>WilsonOriginalTwoFlatPublicMixedSpan.original F simple bliss slow D T h d books
  by_cases ne:Nonempty I
  · haveI:=ne
    filter_upwards [bounds,WilsonOriginalTwoFlatPublicOuter.original F simple bliss 2,
      (wilson_link F simple bliss.budgets bliss.keen bliss.lies).positive] with r funded clock gp
    intro ρ span anchor m j
    obtain ⟨i₀,near⟩:=anchor
    have im:(books (ρ i₀)).W.k ≤ m:=(le_max_right ..).trans
      (Finset.le_sup (f:=fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k) (mem_univ i₀))
    have am:a m ≤ r:=((C).S.strictAnti.antitone im).trans
      (((WilsonReflectedPublicBulbBerth.mesh R _ (books (ρ i₀)).checked).trans (books (ρ i₀)).active.le).trans near.le)
    have inv:((wilson z r)⁻¹)^2 ≤ (β m)^4:=by
      apply (mul_le_mul_iff_of_pos_left clock.1).mp
      simpa only [outer,mul_comm ((β m)^(2*2)) r] using clock.2.2 m am
    have grow:(β m)^4 ≤ (β m)^5:=pow_le_pow_right₀ ((P).fits.delayed m).le (by decide)
    have bill:=((mul_le_mul_of_nonneg_left (inv.trans grow) ((C).S.a_pos j).le).trans
      ((WilsonInvariantActionPosition.arrival R 5 m).2.trans am))
    have first:a j/r ≤ (wilson z r)^2:=by
      rw [div_le_iff₀ clock.1]
      rw [inv_pow,←div_eq_mul_inv,div_le_iff₀ (pow_pos gp 2)] at bill
      exact bill.trans_eq (mul_comm ..)
    exact ⟨first,fun i=>(funded ρ span ⟨i₀,near⟩ |>.2 i).2⟩
  · exact Eventually.of_forall fun _ _ _ ⟨i,_⟩=>False.elim (ne ⟨i⟩)

end YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh

