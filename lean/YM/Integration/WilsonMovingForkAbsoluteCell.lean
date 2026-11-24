import YM.Integration.WilsonMovingForkTranslatedPhase
import YM.Integration.WilsonMovingForkAbsoluteHousing

/-! The same measured field on an absolute window of common cell translates. Only the original unconditioned integral is translated once. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMovingForkAbsoluteCell
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

private theorem average {m:ℕ}(μ:Fin m→ℝ)(pos:∀i,0≤μ i)(one:∑i,μ i=1)
    (Z:ℂ)(Y:Fin m→ℂ)(E:ℝ)(paid:∀k,‖Z-Y k‖≤E):‖Z-∑i,(μ i:ℂ)*Y i‖≤E:=by
  have op:(∑i,(μ i:ℂ))=1:=by exact_mod_cast one
  have eq:Z-∑i,(μ i:ℂ)*Y i=∑i,(μ i:ℂ)*(Z-Y i):=by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,op,one_mul]
  rw [eq]
  refine (norm_sum_le _ _).trans ?_
  calc
    ∑i,‖(μ i:ℂ)*(Z-Y i)‖ ≤ ∑i,μ i*E:=Finset.sum_le_sum fun i _=>by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pos i)]
      exact mul_le_mul_of_nonneg_left (paid i) (pos i)
    _=E:=by rw [←Finset.sum_mul,one,one_mul]

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
      ∀weak:E→Bool,∀m:ℕ,∀shift:Fin m → Cover,∀μ:Fin m→ℝ,(∀i,0≤μ i)→(∑i,μ i=1)→
      (∀k,‖(C).S.gridPoint j (shift k)‖≤B*(C).S.a w)→
      let v(i:E):=homogeneous F Jr Z (ρ i).val (d i).val (x i)
      let Y:=fun os:E → Cover=>word R (fun i:E=>(d i).val) j N p top.le os
        (fun i=>((books (ρ i)).rows (d i)).arm (weak i) (v i) |>.source (N,p))
      let Y':=fun k=>Y (fun i=>o i+shift k)
      let fare:=(∏i:E,K i)*(wilson z r)^p₀
      ‖(C).omega N p (Y o)-∑k,(μ k:ℂ)*reading R (N:=N) (credit (C) N p 0 (Y' k) u (uj.trans top.le)) u le_rfl‖≤fare ∧
        ∀k,Heard R fac.simpleGate N p u (Y' k) fare:=by
  obtain ⟨J,u,stop,K,unit,each⟩:=WilsonMovingForkTranslatedPhase.original F Jr Z fac bliss slow lead paid D T h d x dp books valid
  refine ⟨J,u,stop,K,unit,?_⟩
  intro L b hb lb M B η mn bn size ep p₀ E has
  filter_upwards [each L b hb lb M B η mn bn size ep p₀ E has] with r room
  intro ρ band near j
  obtain ⟨uj,all⟩:=room ρ band near
  refine ⟨uj,?_⟩
  intro w coarse N p top o inside apart weak m shift μ pos one fit v Y Y' fare
  have heard:=fun k=>all w coarse N p top o inside apart weak (shift k) (fit k)
  exact ⟨average μ pos one _ _ fare (fun k=>(heard k).1),fun k=>(heard k).2⟩

end YM.Integration.WilsonMovingForkAbsoluteCell
end
