import YM.Integration.WilsonMovingForkOwnRadiusSites
import YM.Integration.WilsonReceivedChronologicalRosterReporterGap
import YM.Integration.WilsonOriginalTwoFlatPublicMixedMesh
import YM.Integration.WilsonMovingForkOpticalBook
import YM.Integration.WilsonAddressedPublicFirstRoseMovingDate

/-! The booked exterior pays its own physical radius at the common reporter. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterOuterHomeMesh
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

open WilsonMovingForkOpticalBook (reporter)
open WilsonReceivedChronologicalFixedCellFee (factor capture)
open Next.Rank.Station


open WilsonMovingForkOwnRadiusSites (Recorded)
omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D T h:ℕ)(d:I→Fin (D+1)){δ:ℝ}(books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (ext:I)(L:ℝ)(lp:0≤L)(floor:ℕ):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let t:=(ρ ext).val
      let f:=reporter F books ρ
      let c:=WilsonMovingForkOwnRadiusSites.capture R.family.S L r t
      c=WilsonCloseCaptureDate.level R.family.S (16*(r+L*t)) ∧ floor≤c ∧ c+2≤f ∧
        a c/a f≤(β f)^(2*T+13+2*h) ∧
      ∀{n:ℕ}(o:Fin n→Lattice.Cover),(∀i,‖R.family.S.gridPoint f (o i)‖≤L*t)→Recorded R f c o:=by
  classical
  let size:=16*(1+L)
  have sp:0<size:=by dsimp [size];positivity
  obtain ⟨need,gap⟩:=eventually_atTop.mp (WilsonReceivedChronologicalRosterReporterGap.original R simple slow (by norm_num:0<(16:ℝ)))
  obtain ⟨hot,heat⟩:=eventually_atTop.mp ((hat_rate (P) simple).eventually_ge_atTop (3*size))
  let limit:=max need hot
  have close:0<a floor/size:=div_pos (R.family.S.a_pos _) sp
  filter_upwards [WilsonOriginalTwoFlatPublicMixedMesh.original F simple bliss slow D T h d books,
    (longer F simple bliss h).eventually (Ioc_mem_nhdsGT close),Ioc_mem_nhdsGT (R.family.S.a_pos (limit+1))]
    with r bought room small
  intro ρ located nearest t f c
  obtain ⟨i,home⟩:=nearest
  have extLive:=located ext
  have rp:=small.1
  let m:=univ.sup fun v=>max (books (ρ v)).stock.j (books (ρ v)).W.k
  have im:(books (ρ i)).W.k ≤ m:=(le_max_right ..).trans
    (Finset.le_sup (f:=fun v=>max (books (ρ v)).stock.j (books (ρ v)).W.k) (mem_univ i))
  have am:a m ≤ r:=((C).S.strictAnti.antitone im).trans
    (((WilsonReflectedPublicBulbBerth.mesh R _ (books (ρ i)).checked).trans (books (ρ i)).active.le).trans home.le)
  have late:limit ≤ m:=by
    by_contra! early
    exact (not_lt_of_ge (am.trans small.2)) ((C).S.strictAnti (by omega:m < limit+1))
  have mf:m≤f:=(WilsonInvariantActionPosition.arrival R 5 m).1.le
  have af:a f≤r:=((C).S.strictAnti.antitone mf).trans am
  have upper:WilsonMovingForkOwnRadiusSites.size L r t≤a floor:=by
    rw [WilsonMovingForkOwnRadiusSites.expanded L rp]
    have bound:=add_le_add (extLive.1.trans extLive.2) (mul_le_mul_of_nonneg_left extLive.2 lp)
    have amount:outer z h r*size≤a floor:=(le_div_iff₀ sp).mp room.2
    dsimp [size] at amount
    change r+L*t≤outer z h r+L*outer z h r at bound
    linarith only [bound,amount]
  have first:=upper.trans ((C).S.strictAnti.antitone (Nat.zero_le floor))
  have bracket:=WilsonMovingForkOwnRadiusSites.issued R lp rp (rp.le.trans extLive.1) first af
  obtain ⟨cf,_,below,above⟩:=bracket
  have past:floor≤c:=by
    by_contra! early
    exact (not_lt_of_ge ((C).S.strictAnti.antitone (by omega:c+1≤floor))) (below.trans_le upper)
  have draw:WilsonMovingForkOwnRadiusSites.size L r t=16*(r+L*t):=WilsonMovingForkOwnRadiusSites.expanded L rp t
  have vpos:0<t:=rp.trans_le extLive.1
  have large:16*r≤a c:=by rw [draw] at above;linarith only [above,mul_nonneg lp vpos.le]
  have visits:c+2≤f:=gap m ((le_max_left ..).trans late) am large
  have openFace:a (c+1)<size*t:=by
    rw [draw] at below
    dsimp [size]
    linarith only [below,extLive.1]
  have earned:t≤(β f)^(2*T+11+2*h)*a f:=(bought ρ located ⟨i,home⟩).2 ext
  have bill:=WilsonAddressedPublicFirstRoseCaptureWidth.original R simple slow vpos sp cf openFace
    (heat f (((le_max_right ..).trans late).trans mf)) earned
  refine ⟨congrArg (WilsonCloseCaptureDate.level R.family.S) draw,past,visits,?_,?_⟩
  · simpa only [show 2*T+11+2*h+2=2*T+13+2*h by omega] using bill
  · intro n o held
    exact WilsonMovingForkOwnRadiusSites.recorded R lp rp vpos.le first af o held

end YM.Integration.WilsonReceivedChronologicalRosterOuterHomeMesh
