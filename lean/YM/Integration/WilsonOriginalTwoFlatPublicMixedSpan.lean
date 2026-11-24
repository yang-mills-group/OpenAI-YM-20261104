import YM.Integration.WilsonOriginalTwoFlatPublicMovingSelection
/-! One public date works for all named detector radii in the physical
polynomial window, including a face omitting the arm that sets the date. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan
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
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ}, (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) →
      (∃i,(ρ i).val=r) →
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let j:=berth R 5 m
      a j ≤ r ∧ ∀i,(max (books (ρ i)).stock.j (books (ρ i)).W.k ≤ j ∧ (ρ i).val ≤ (β j)^(2*T+11+2*h)*a j):=by
  have geo:=WilsonOriginalTwoFlatPublicGeometry.original F simple bliss slow T 0 0 (M:=1) (η:=1) (le_refl 1) zero_lt_one
  obtain ⟨δ',good,geom⟩:=Metric.mem_nhdsWithin_iff.mp geo
  have later:=longer F simple bliss h
  filter_upwards [later.eventually ((gt_mem_nhds good).filter_mono nhdsWithin_le_nhds),WilsonOriginalTwoFlatPublicOuter.original F simple bliss h] with r tiny clock
  intro ρ span near m j
  have mj:m ≤ j:=(WilsonInvariantActionPosition.arrival R 5 m).1.le
  have inj(i:I):max (books (ρ i)).stock.j (books (ρ i)).W.k ≤ j:=
    (Finset.le_sup (f:=fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k) (mem_univ i)).trans mj
  obtain ⟨i₀,anchor⟩:=near
  have aj:a j ≤ r:=((C).S.strictAnti.antitone ((le_max_right ..).trans (inj i₀))).trans
    (((WilsonReflectedPublicBulbBerth.mesh R _ (books (ρ i₀)).checked).trans (books (ρ i₀)).active.le).trans anchor.le)
  obtain ⟨i₁,_,peak⟩:=Finset.exists_mem_eq_sup univ univ_nonempty (fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k)
  change m=max _ _ at peak
  have spec:=geom (show (ρ i₁).val∈Metric.ball (0:ℝ) δ' ∩ Set.Ioi 0 from ⟨by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (ρ i₁).property.1]
    exact (span i₁).2.trans_lt tiny,(ρ i₁).property.1⟩)
    ((books (ρ i₁)).rows (d i₁)) (books (ρ i₁)).checked (books (ρ i₁)).active
  change _ ≤ berth R 5 (max _ _) ∧ _ at spec
  rw [←peak] at spec
  have rj:r ≤ (β j)^(2*T+11)*a j:=by
    refine (span i₁).1.trans (le_trans ?_ spec.2.2.2.2.1)
    nlinarith only [(ρ i₁).property.1]
  refine ⟨aj,fun i=>⟨inj i,?_⟩⟩
  calc
    _ ≤ outer z h r:=(span i).2
    _ ≤ (β j)^(2*h)*r:=clock.2.2 j aj
    _ ≤ (β j)^(2*h)*((β j)^(2*T+11)*a j):=mul_le_mul_of_nonneg_left rj (pow_nonneg (zero_le_one.trans ((P).fits.delayed j).le) _)
    _ = _:=by rw [pow_add];ring

end YM.Integration.WilsonOriginalTwoFlatPublicMixedSpan

