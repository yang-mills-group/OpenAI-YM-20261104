import YM.Integration.WilsonThermometerWeakFourMeasuredMenu
import YM.Integration.WilsonAddressedCorrectedAlignedSource

/-! One reporting date, three exact nominated Wilson columns, with the
original grade-six origin and independently displaced grade-four residues. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakNominatedTriple
open Function Filter Set Lattice RG Wilson Spec Extraction Cells
open YM.Integration.WilsonLimitConstruction
open PhysicalNext.Repeat.Legato Next.Rank Next.Rank.Tapes.West Next.Rank.East
open PhysicalNext.RankCovariance MergeProof.East Trace.Over
open scoped Topology Classical

open PhysicalNext PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Ship Next.Rank.Station Next.Rank.Spindle
open Function Filter Set Metric Source RG12 Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Cells Extraction
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Tapes.West Configuration Normal Rise
open Paint Thirst Relation Perch Glimmer LiftMark Beamer Station Atlas Tariffs Ribbon
open Edition Peak Value Marker Corona Alarm Next.Rank.Glyph
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonAddressedWeakCalibration WilsonAddressedWeakReflectedHearing WilsonThermometerReflectedTrajectory
open FVA2 FVA2.ColorCode Pert.Position MS MS.Land MS.Menus MS.Rake MS.Tone PhysMS
open Trace Trace.Pilot WilsonAddressedWeakCorrectedCylinder WilsonAddressedWeakPointCells WilsonAddressedWeakMaxwellPositions
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

open Function Filter Set Table Spec Extraction OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open Lattice Wilson RG RG12 Labels Extra.Histories RG05Readout Native Address Many Records Harvest Push.GridApprox Push.Local
open PhysicalNext.Repeat.Legato MergeProof Accent Trace.Physical Trace.Physical.GermGraph Work.G08 Next.Rank
open RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerReading
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionCorrectedCap
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open scoped BigOperators Classical Topology
open Next.Extract Push PhysicalNext.RankCovariance Pert Pert.Position MS.Land MS.Menus
open WilsonPositionThermometerStationNorm
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {T:Table R.family.book}
variable {D:Local.Physical.Deck G} {O:Booked D} (M:MS_Data G O)
variable (V₀:∀d,Source.SectionData (R.family.labels.level d)) (W:Mark.Weave G)
    {P₀:∀d,(ℕ×ℕ)→(R.family.label d≃ₗ[ℂ]R.family.label d)} (b:Presentation R.family)
    (house:Hearthside R.family V₀ W P₀ b (PhysicalNext.Repeat.Legato.Bandage.fly R.alloy.B.a))
variable (F:Final R.family f T) (P:ℝ→tower T) (V:Store G) {H:(Bel R.family.book).Hierarchy}
    {l:Ultrafilter (ℕ×ℕ)} (A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6)
local notation "C" => R.family
local notation "Lev" => R.family.path.levels
local notation "cash" => WilsonThermometerOffsetLedger.cash R
private abbrev armGrade := WilsonPositionThermometerGradedSource.grade

def paid (Z:WilsonPositionThermometerCapStation.Group C 6) (k N p:ℕ) (hk:k≤N)
    (s:Badge) (r:∀i:Fin 3,Emblems C (armGrade i)) (E:ℝ):Prop:=
    ∃y:∀i:Fin 3,Palette C (armGrade i),∀i:Fin 3,
      (((C).S.a k:ℂ)^(armGrade i).val) • ((C).factory (armGrade i) N p).terminal
        (finer (r i) hk (y i) (primaryLetter (armGrade i)))=
        Z.station.wheel.atCut (N,p) (index Z (armGrade i)) (vector Z s i) ∧
      size (y i)≤ E*WilsonThermometerMarchReference.fee (C) s i

include M V₀ W b house
theorem original (simple:G.Simple) (panels:R2I.RG05Joint.AcrossPanels R.kit)
    (shop:RG05Preconstruction.ReadoutPurchase R.b) (rules:Rules G) (warehouse:Warehouse G)
    (book:Book (f:=f) (l:=l) (H:=H) A P) (lead:Leading F P) (μ ε:ℝ) (ep:0<ε):
    ∃E:ℝ,0≤E ∧ ∀floor:ℕ,∀ᶠ t:ℝ in trail,let Z:=adjusted F P V A t
      ∃k:ℕ,floor≤k ∧ ∃later:k≤Z.station.k,
      (C).S.a k/(C).S.a Z.station.k≤(Lev).clock.hatBeta Z.station.k^ε ∧
      ∀ᶠ N:ℕ in atTop,∃late:Z.station.k<N,∀p,
      ∀(z:Fin 3→Site ((C).side N p)) (Q:∀i:Fin 3,Sight C (armGrade i) p)
        (r:∀i:Fin 3,Emblems C (armGrade i)), z 0=0 →
        (∀i,Enrolled R.makes R.doors cash k N p (armGrade i) (digits R N p (z i)) (Q i) (r i)) →
        ∀s:Badge, paid Z k N p (later.trans late.le) s r (E*((Lev).clock.hatBeta Z.station.k)^ε):=by
  let η:=ε/2
  let τ:=min 1 η
  have hp:0<η:=by unfold η;positivity
  have ht:0<τ:=lt_min zero_lt_one hp
  obtain ⟨E,nonneg,lower⟩:=WilsonThermometerWeakFourMeasuredMenu.withSpan R M V₀ W b house simple panels shop rules warehouse μ ε ep f H
  let d:=fun a:Badge×Fin 3=>armGrade a.2
  let inputs:∀a:Badge×Fin 3,(Bel (C).book).Field (d a):=fun a=>WilsonPositionThermometerGradedSource.source (C) a.1 a.2
  have receive (m:ℕ):=WilsonPositionCorrectedCap.mixed F P V A book lead d inputs m
  have go:Tendsto (fun t=>(adjusted F P V A t).station.k) trail atTop:=
    tendsto_atTop.mpr fun m=>(receive m).mono fun _ h=>h.1
  have refs:∀ᶠ k:ℕ in atTop,∀e:Fin 7,(C).ref e≤k:=eventually_all.mpr fun e=>eventually_ge_atTop _
  obtain ⟨base,extra⟩:=eventually_atTop.mp ((open_late (C) simple 6).and refs)
  let J:=max E 2
  have hJ:0≤J:=nonneg.trans (le_max_left ..)
  refine ⟨J,hJ,?_⟩
  intro floor
  filter_upwards [receive 0,go.eventually (lower (max floor base) τ ht (min_le_left ..)),
    WilsonAddressedCorrectedAlignedFare.original F P V A simple book lead η hp] with t filed station reward
  let Z:=adjusted F P V A t
  dsimp only
  obtain ⟨k,start,later,span,issued⟩:=station
  let β:ℝ:=(Lev).clock.hatBeta Z.station.k
  have βlarge:1≤β:=((Lev).fits.delayed _).le
  have cashSpan:(C).S.a k/(C).S.a Z.station.k≤β^η:=
    span.trans (Real.rpow_le_rpow_of_exponent_le βlarge (min_le_right ..))
  obtain ⟨opening,ceil⟩:=extra k (by omega)
  refine ⟨k,(le_max_left ..).trans start,later,cashSpan.trans (Real.rpow_le_rpow_of_exponent_le βlarge (by dsimp [η];linarith)),?_⟩
  filter_upwards [issued] with N table
  obtain ⟨late,posted⟩:=table
  refine ⟨late,?_⟩
  intro per z Q r origin registered s
  let hk:=later.trans late.le
  let x:=fun i:Fin 3=>Z.station.wheel.atCut (N,per) (index Z (armGrade i)) (vector Z s i)
  have normed(i:Fin 3):cost (C) (armGrade i)*‖vector Z s i‖≤WilsonThermometerMarchReference.fee (C) s i:=by
    have error:‖vector Z s i-WilsonPositionThermometerGradedSource.source (C) s i‖≤costHint 0:=filed.2.2.2.2.2 (s,i)
    have lim:=norm_le_norm_sub_add (vector Z s i) (WilsonPositionThermometerGradedSource.source (C) s i)
    have weight:0≤cost (C) (armGrade i):=by unfold cost;positivity
    exact mul_le_mul_of_nonneg_left (by linarith only [error,lim]) weight
  have cashPos (i:Fin 3):0≤WilsonThermometerMarchReference.fee (C) s i:=
    (mul_nonneg (by unfold cost;positivity) (norm_nonneg _)).trans (normed i)
  have column (i:Fin 2): ∃y:Palette C (armGrade i.succ),
      (((C).S.a k:ℂ)^(armGrade i.succ).val) • ((C).factory (armGrade i.succ) N per).terminal
        (finer (r i.succ) hk y (primaryLetter (armGrade i.succ)))=x i.succ ∧
      size y≤(J*β^ε)*WilsonThermometerMarchReference.fee (C) s i.succ:=by
    let j:=index Z (armGrade i.succ)
    have shelf:4≤Z.horizon:=Nat.le_of_lt_succ j.isLt
    obtain ⟨y,identity,wage⟩:=posted per (z i.succ) (Q i.succ) (r i.succ) (registered i.succ) Z.station shelf (vector Z s i.succ) rfl filed.2.1
    refine ⟨y,identity,wage.trans ?_⟩
    have coeff:0≤E*β^ε:=mul_nonneg nonneg (Real.rpow_nonneg (zero_le_one.trans βlarge) _)
    exact (mul_le_mul_of_nonneg_left (normed i.succ) coeff).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left E 2) (Real.rpow_nonneg (zero_le_one.trans βlarge) _)) (cashPos _))
  choose ly leq lprice using column
  have center:=registered 0
  rw [origin] at center
  have hr (e:ℕ)(bound:e≤6):(C).ref e≤N:=(ceil ⟨e,by omega⟩).trans hk
  obtain ⟨exactSix,upper⟩:=WilsonAddressedAlignedColumn.original R center hk le_rfl hr (opening per) (x 0)
  have pays:=reward N per late s 0 k (opening per).post later
  let y₀:=WilsonAddressedAlignedColumn.offer R (x 0) (opening per) hk
  have six:size y₀≤(J*β^ε)*WilsonThermometerMarchReference.fee (C) s 0:=by
    have paid₀:=upper.trans (mul_le_mul_of_nonneg_left pays (by norm_num))
    have βpos:0≤β^η:=Real.rpow_nonneg (zero_le_one.trans βlarge) _
    let fee:=WilsonThermometerMarchReference.fee (C) s 0
    calc
      _ ≤ 2*(((C).S.a k/(C).S.a Z.station.k)*(β^η*fee)):=paid₀
      _ ≤ 2*(β^η*(β^η*fee)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right cashSpan (mul_nonneg βpos (cashPos _))) (by norm_num)
      _ = (2*β^ε)*fee:=by rw [←mul_assoc (β^η),←Real.rpow_add (zero_lt_one.trans_le βlarge),show η+η=ε by dsimp [η];ring];ring
      _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.rpow_nonneg (zero_le_one.trans βlarge) _)) (cashPos _)
  refine ⟨Fin.cases y₀ ly,?_⟩
  intro i
  exact Fin.cases ⟨exactSix,six⟩ (fun j=>⟨leq j,lprice j⟩) i

end YM.Integration.WilsonThermometerWeakNominatedTriple
end
