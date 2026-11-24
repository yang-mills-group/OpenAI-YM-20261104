import YM.Integration.WilsonMovingForkCommonTranslation
import YM.Integration.WilsonMovingForkAbsoluteHousing

/-! The same measured field on an absolute window of common cell translates. Only the original unconditioned integral is translated once. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkTranslatedPhase
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
open MS MS.Land FVA2 FVA2.Register


open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

open WilsonMovingForkAbsolutePhase (Sampled)
open WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFourSquare

private theorem grid_add (j:ℕ)(o t:Cover):
    (C).S.gridPoint j (o+t)=(C).S.gridPoint j o+(C).S.gridPoint j t:=by
  ext1 k;change (C).S.a j*(((o+t) k:ℤ):ℝ)=(C).S.a j*(o k:ℝ)+(C).S.a j*(t k:ℝ)
  simp [mul_add]

theorem original (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (D T h:ℕ)(d:I→Fin (D+1))(x:∀i,RG17.Free C (d i).val){δ:ℝ}(dp:0<δ)
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (valid:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃J u:ℕ,Stop C 0 J u ∧ ∃K:I→ℝ,(∀i,1≤K i) ∧
      ∀L b:ℕ,h≤b→L≤b→∀M B η:ℝ,0≤M→0≤B→1≤M+B→0<η→
      ∀p₀:ℕ,∀E:Finset I,E.Nonempty → ∀ᶠr in trail,∀ρ:I→{s:ℝ //0<s ∧ s<δ},
      (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let j:=WilsonMovingForkOpticalBook.reporter F books ρ
      ∃uj:u≤j,∀w:ℕ,(C).S.a w≤outer z L r→∀N p:ℕ,∀top:j<N,∀o:E → Cover,
      (∀i,‖(C).S.gridPoint j (o i)‖≤M*outer z h r)→
      (Pairwise fun i k=>η*r≤‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o k)‖)→
      ∀weak:E→Bool,∀shift:Cover,‖(C).S.gridPoint j shift‖≤B*(C).S.a w→
      let v(i:E):=homogeneous F Jr Z (ρ i).val (d i).val (x i)
      let Y:=fun os:E → Cover=>word R (fun i:E=>(d i).val) j N p top.le os
        (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p))
      let Y':=Y (fun i=>o i+shift)
      let fare:=(∏i:E,K i)*(wilson z r)^p₀
      ‖(C).omega N p (Y o)-reading R (N:=N) (credit (C) N p 0 Y' u (uj.trans top.le)) u le_rfl‖≤fare ∧
        Heard R fac.simpleGate N p u Y' fare:=by
  obtain ⟨J,u,stop,K,unit,each⟩:=WilsonMovingForkAbsolutePhase.selected F Jr Z fac bliss slow lead paid D T h d x dp books valid
  refine ⟨J,u,stop,K,unit,?_⟩
  intro L b hb lb M B η mn bn size ep p₀ E has
  let law:=wilson_link F fac.simpleGate bliss.budgets bliss.keen bliss.lies
  filter_upwards [each b hb (M+B) η size ep p₀ E has,law.positive,(law.conforms fac.simpleGate).eventually (ge_mem_nhds zero_lt_one)]
    with r room gp small
  intro ρ band near j
  obtain ⟨uj,all⟩:=room.2.2 ρ band near
  refine ⟨uj,?_⟩
  intro w coarse N p top o inside apart weak shift fit v Y Y' fare
  have expands(k:ℕ)(kb:k≤b):outer z k r≤outer z b r:=mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ((one_le_inv₀ gp).mpr small) kb) room.1.le
  have houses(i:E):‖(C).S.gridPoint j (o i+shift)‖≤(M+B)*outer z b r:=by
    rw [grid_add,add_mul]
    exact (norm_add_le _ _).trans (add_le_add
      ((inside i).trans (mul_le_mul_of_nonneg_left (expands _ hb) mn))
      (fit.trans (mul_le_mul_of_nonneg_left (coarse.trans (expands _ lb)) bn)))
  have far:Pairwise fun i k=>η*r≤‖(C).S.gridPoint j (o i+shift)-(C).S.gridPoint j (o k+shift)‖:=by
    intro i k ik;simpa only [grid_add,add_sub_add_right_eq_sub] using apart ik
  have heard:=all N p top (fun i=>o i+shift) houses far weak
  have move:(C).omega N p Y'=(C).omega N p (Y o):=WilsonMovingForkCommonTranslation.original R _ _ _ _ _
  refine ⟨?_,heard.2⟩
  rw [←move];exact heard.1

end YM.Integration.WilsonMovingForkTranslatedPhase
end
