import YM.Integration.WilsonMovingForkElectedCaptureWidth
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh

/-! Actual optical return for a growing support on the elected heterogeneous physical book. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingForkElectedCaptureStops
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
  {I:Type}[Fintype I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS

open Next.Rank.Station (hat_rate)
open Pert.Asymptotics
theorem original (simple : G.Simple) (bliss : Bliss F l z H)
    (slow : WilsonWindowReportingPace.Slow R.kit) (D T B reserve depth : ℕ)
    (d : I → Fin (D+1)) {δ : ℝ}
    (books : (s : {s : ℝ // 0<s ∧ s<δ}) → Book F (l:=l) H z D T s.val)
    {L : ℝ} (lp : 0 ≤ L) :
    ∃ width : ℕ, ∀ᶠ r in trail, ∀ (ρ : I → {s : ℝ // 0<s ∧ s<δ}),
      (∀ i, r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z B r) → (∃ i, (ρ i).val = r) →
      ∀ t, r ≤ t → t ≤ outer z B r →
      let f := berth R 5 (univ.sup fun i => max (books (ρ i)).stock.j (books (ρ i)).W.k)
      let K := berth R reserve f
      let c := WilsonCloseCaptureDate.level R.family.S (16*(1+L*(t/r))*r)
      c ≤ f ∧ a c/a f ≤ (β f)^((2*T+11+2*B)+2*B+2) ∧
      ∀ v N per, v ≤ c → c ≤ N →
        R.family.S.scale c-R.family.S.scale v ≤
          4*(2*(depth:ℝ)+1)*Real.log (regulatorRun R.family N per c)⁻¹ →
        a v/a K ≤ (β v)^width ∧ R.family.S.scale K-R.family.S.scale v ≤
          (width:ℝ)*(1+Real.log (β (v+1))) := by
  let trust := 2*T+11+2*B
  obtain ⟨width,pr⟩ := WilsonMovingForkOpticalStops.original R simple slow reserve (trust+2*B+2) depth
  obtain ⟨floor,school⟩ := eventually_atTop.mp pr
  obtain ⟨onset,heat⟩ := eventually_atTop.mp
    ((hat_rate R.family.path.levels simple).eventually_ge_atTop (48*(1+L)))
  refine ⟨width,?_⟩
  have raw := wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have fixed : 0 < a 0/(16*(1+L)) := div_pos (R.family.S.a_pos _) (by positivity)
  have close := (longer F simple bliss B).eventually (Ioc_mem_nhdsGT fixed)
  filter_upwards [WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T B d books,
    WilsonOriginalTwoFlatPublicOuter.original F simple bliss B,raw.positive,
    (Coupling.conforms simple raw).eventually (ge_mem_nhds zero_lt_one),close,
    Ioc_mem_nhdsGT (R.family.S.a_pos (max floor onset))]
    with r booked outerRate gp gu small late
  intro ρ homes nearest t rt top f K c
  have rp := outerRate.1
  have mesh := booked ρ homes nearest
  have af : a f ≤ r := by
    have issued := (div_le_iff₀ rp).mp mesh.1
    exact issued.trans ((mul_le_mul_of_nonneg_right (pow_le_one₀ gp.le gu) rp.le).trans_eq (one_mul _))
  have ff : max floor onset ≤ f := by
    by_contra! early
    exact (R.family.S.strictAnti early).not_ge (af.trans late.2)
  let M := 16*(1+L*(t/r))
  have tp : 0 ≤ t/r := div_nonneg (rp.le.trans rt) rp.le
  have mp : 0 < M := by dsimp [M];positivity
  have room : M*r ≤ a 0 := by
    have id : M*r = 16*(r+L*t) := by dsimp [M];field_simp
    have lim := (le_div_iff₀ (show 0<16*(1+L) by positivity)).mp small.2
    rw [id]
    have bound : r+L*t ≤ outer z B r+L*outer z B r :=
      add_le_add (rt.trans top) (mul_le_mul_of_nonneg_left top lp)
    linarith only [bound,lim] 
  have bracket := WilsonCloseCaptureDate.bracket R.family.S (mul_pos mp rp) room
  have cb : c ≤ f := by
    by_contra! opposite
    have cover : r ≤ M*r := by
      apply le_mul_of_one_le_left rp.le
      dsimp [M];linarith only [mul_nonneg lp tp]
    exact (R.family.S.strictAnti opposite).not_ge (af.trans (cover.trans bracket.2))
  have pace : t/r ≤ (β f)^(2*B) := (div_le_iff₀ rp).mpr (top.trans (outerRate.2.2 f af))
  obtain ⟨i,home⟩ := nearest
  have income : r ≤ (β f)^trust*a f := home ▸ (mesh.2 i)
  have paid := WilsonMovingForkElectedCaptureWidth.original R simple slow rp lp tp cb bracket.1
    (heat f ((le_max_right _ _).trans ff)) pace income
  refine ⟨cb,paid,?_⟩
  intro v N per vc cn date
  exact school f ((le_max_left _ _).trans ff) c v N per cb vc cn paid date

end YM.Integration.WilsonMovingForkElectedCaptureStops
