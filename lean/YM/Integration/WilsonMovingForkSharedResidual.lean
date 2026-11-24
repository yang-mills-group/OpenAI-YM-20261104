import YM.Integration.WilsonMovingForkSharedStop
import YM.Integration.WilsonMovingForkTrueCell

/-! Actual lifted samples of every proper face at the nominated prior after one whole-cell shift. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkSharedResidual
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

open WilsonPositionProgramTrialCellDigits (residual)
open WilsonPositionProgramTrialCenterHousing (grid_sub anchor_bound)

omit [DecidableEq I] [Nonempty I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(D T h:ℕ)(d:I→Fin (D+1))
    (x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)(u:ℕ)(K:I→ℝ)
    (L b:ℕ)(hb:h≤b)(lb:L≤b)(M η:ℝ)(mn:0≤M)
    (sale:WilsonMovingForkAbsolutePhase.Sampled F Jr Z simple D T h b d x (M+1) η δ books u K)
    (p₀:ℕ)(E:Finset I)(has:E.Nonempty):
    ∀ᶠr in trail,∀ρ:I→{s:ℝ //0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let j:=WilsonMovingForkOpticalBook.reporter F books ρ
      ∃uj:u≤j,∀w:ℕ,∀wj:w≤j,(C).S.a w≤outer z L r→∀N p:ℕ,∀top:j<N,∀o:I → Cover,∀anchor:I,
      (∀i:E,‖(C).S.gridPoint j (o i-o anchor)‖≤M*outer z h r)→
      (Pairwise fun i k:E=>η*r≤‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o k)‖)→
      ∀weak:E→Bool,∀center:Cover,
      let v(i:E):=homogeneous F Jr Z (ρ i).val (d i).val (x i)
      let Y:=fun os:E → Cover=>word R (fun i:E=>(d i).val) j N p top.le os
        (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p))
      let Y':=Y (fun i:E=>residual (C).S wj (fun t:I=>o t+center) anchor i)
      let fare:=(∏i:E,K i)*(wilson z r)^p₀
      ‖(C).omega N p (Y (fun i:E=>o i))-reading R (N:=N) (credit (C) N p 0 Y' u (uj.trans top.le)) u le_rfl‖≤fare ∧
        Heard R simple N p u Y' fare:=by
  let law:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  filter_upwards [sale p₀ E has,law.positive,(law.conforms simple).eventually (ge_mem_nhds zero_lt_one)]
    with r room gp small
  intro ρ band near j
  obtain ⟨uj,all⟩:=room.2.2 ρ band near
  refine ⟨uj,?_⟩
  intro w wj coarse N p top o anchor inside apart weak center v Y source fare
  let loc:I → Cover:=fun i=>o i+center
  let os:E → Cover:=fun i=>residual (C).S wj loc anchor i
  have expands(k:ℕ)(kb:k≤b):outer z k r≤outer z b r:=mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ ((one_le_inv₀ gp).mpr small) kb) room.1.le
  have fit(i:E):‖(C).S.gridPoint j (os i)‖≤(M+1)*outer z b r:=by
    have fit:=WilsonPositionProgramTrialCenterHousing.original (C).S wj loc anchor (i:I)
    simp only [loc,add_sub_add_right_eq_sub] at fit
    refine fit.trans ?_
    rw [add_mul,one_mul,add_comm (M*outer z b r)]
    exact add_le_add (coarse.trans (expands _ lb)) ((inside i).trans (mul_le_mul_of_nonneg_left (expands _ hb) mn))
  have far:Pairwise fun i k:E=>η*r≤‖(C).S.gridPoint j (os i)-(C).S.gridPoint j (os k)‖:=by
    intro i k ik
    rw [← WilsonPositionProgramTrialCenterHousing.grid_sub,WilsonPositionProgramTrialCellDigits.relative]
    simpa only [loc,add_sub_add_right_eq_sub,WilsonPositionProgramTrialCenterHousing.grid_sub] using apart ik
  have read:=all N p top os fit far weak
  let shift:=center-(R.family.S.toDepth wj 0).count.val • WilsonPositionProgramTrialCellDigits.ancestor (C).S wj loc anchor
  have move:(C).omega N p source=(C).omega N p (Y (fun i:E=>o i)):=by
    have exactSites(i:E):os i=o i+shift:=by
      dsimp [os,WilsonPositionProgramTrialCellDigits.residual,loc,shift]
      abel
    simpa only [Y,source,←exactSites] using WilsonMovingForkCommonTranslation.original R _ top.le
      (fun i:E=>o i) (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p)) shift
  refine ⟨?_,read.2⟩
  rw [←move]
  exact read.1

end YM.Integration.WilsonMovingForkSharedResidual
end
