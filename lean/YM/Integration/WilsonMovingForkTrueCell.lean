import YM.Integration.WilsonMovingForkAbsoluteCell
import YM.Integration.WilsonPositionProgramTrialCenterHousing
import YM.Integration.WilsonMovingForkAbsoluteHousing

/-! The same measured field on an absolute window of common cell translates. Only the original unconditioned integral is translated once. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkTrueCell
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

theorem original (fac:Facilities C order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (D T h:ℕ)(d:I→Fin (D+1))(x:∀i,RG17.Free C (d i).val){δ:ℝ}(dp:0<δ)
    (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (valid:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃J u:ℕ,Stop C 0 J u ∧ ∃K:I→ℝ,(∀i,1≤K i) ∧
      ∀L b:ℕ,h≤b→L≤b→∀M η:ℝ,0≤M→0<η→
      ∀p₀:ℕ,∀E:Finset I,E.Nonempty → ∀ᶠr in trail,∀ρ:I→{s:ℝ //0<s ∧ s<δ},
      (∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let j:=WilsonMovingForkOpticalBook.reporter F books ρ
      ∃uj:u≤j,∀w:ℕ,∀wj:w≤j,(C).S.a w≤outer z L r→∀N p:ℕ,∀top:j<N,∀o:I → Cover,∀anchor:I,
      (∀i:E,‖(C).S.gridPoint j (o i-o anchor)‖≤M*outer z h r)→
      (Pairwise fun i k:E=>η*r≤‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o k)‖)→
      ∀weak:E→Bool,∀m:ℕ,∀center:Fin m → Cover,∀μ:Fin m→ℝ,(∀i,0≤μ i)→(∑i,μ i=1)→
      let v(i:E):=homogeneous F Jr Z (ρ i).val (d i).val (x i)
      let Y:=fun os:E → Cover=>word R (fun i:E=>(d i).val) j N p top.le os
        (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p))
      let Y':=fun k=>Y (fun i:E=>residual (C).S wj (fun t:I=>o t+center k) anchor i)
      let fare:=(∏i:E,K i)*(wilson z r)^p₀
      ‖(C).omega N p (Y (fun i:E=>o i))-∑k,(μ k:ℂ)*reading R (N:=N) (credit (C) N p 0 (Y' k) u (uj.trans top.le)) u le_rfl‖≤fare ∧
        ∀k,Heard R fac.simpleGate N p u (Y' k) fare:=by
  obtain ⟨J,u,stop,K,unit,each⟩:=WilsonMovingForkAbsoluteCell.original F Jr Z fac bliss slow lead paid D T h d x dp books valid
  refine ⟨J,u,stop,K,unit,?_⟩
  intro L b hb lb M η mn ep p₀ E has
  filter_upwards [each L b hb lb M 1 η mn zero_le_one (by linarith) ep p₀ E has] with r room
  intro ρ band near j
  obtain ⟨uj,all⟩:=room ρ band near
  refine ⟨uj,?_⟩
  intro w wj coarse N p top o anchor inside apart weak m center μ pos one v Y Y' fare
  let base:E → Cover:=fun i=>o i-o anchor
  let loc:=fun k t=>o t+center k
  let slide:=fun k=>residual (C).S wj (loc k) anchor anchor
  have size(k):‖(C).S.gridPoint j (slide k)‖≤1*(C).S.a w:=by rw [one_mul];exact anchor_bound (C).S wj (loc k) anchor
  have dist:Pairwise fun i k:E=>η*r≤‖(C).S.gridPoint j (base i)-(C).S.gridPoint j (base k)‖:=by
    intro i k ik;simpa only [base,grid_sub,sub_sub_sub_cancel_right] using apart ik
  have heard:=all w coarse N p top base inside dist weak m slide μ pos one size
  have roots(k)(i:E):base i+slide k=residual (C).S wj (loc k) anchor i:=by
    have keep:=WilsonPositionProgramTrialCellDigits.relative (C).S wj (loc k) anchor i anchor
    dsimp only [base,slide,loc] at *
    simp only [add_sub_add_right_eq_sub] at keep
    rw [←keep,sub_add_cancel]
  have orig:(C).omega N p (Y base)=(C).omega N p (Y fun i:E=>o i):=by
    simpa only [Y,base,sub_eq_add_neg] using WilsonMovingForkCommonTranslation.original R _ top.le
      (fun i:E=>o i) (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p)) (-o anchor)
  let row(k):=Y (fun i=>base i+slide k)
  have cols(k):row k=Y' k:=congrArg Y (funext (roots k))
  change ‖(C).omega N p (Y base)-∑k,(μ k:ℂ)*reading R (N:=N) (credit (C) N p 0 (row k) u (uj.trans top.le)) u le_rfl‖≤fare ∧
    ∀k,Heard R fac.simpleGate N p u (row k) fare at heard
  simpa only [cols,orig] using heard

end YM.Integration.WilsonMovingForkTrueCell
end
