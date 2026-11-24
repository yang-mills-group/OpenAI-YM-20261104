import YM.Integration.WilsonOriginalObservedRosePooledWrap
import YM.Integration.WilsonMovingForkSlotDate
import YM.Integration.WilsonMovingForkHomeIncome

/-! The original department slots and their numerical incomes before either regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePooledPurse
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
  {n:ℕ}[Nonempty (Fin n)]
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


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)


open WilsonMovingForkSlotDate (slot)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalObservedRosePooledWrap (allowance)
open WilsonOriginalObservedRoseMeshHeight (variation)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)

def reading {D T:ℕ}{r:ℝ}(b:Book F (l:=l) H z D T r)(d:Fin (D+1))(x:RG17.Free (C) d.val):=
  slot F b d (homogeneous F Jr Z r d.val x)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (cap:∀j,((P).budget j).supportExponent≤100)(D T h:ℕ)(d:Fin n→Fin (D+1))
    (x:∀i,RG17.Free (C) (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    ∃(M:Fin n→ℝ)(E:Fin n→ℕ),(∀i,0≤M i) ∧ ∀gate:ℕ,∀ᶠr in trail,
      ∀ρ:Fin n→{s:ℝ // 0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      ∀i,let L:=reading F Jr Z (books (ρ i)) (d i) (x i)
         gate≤L.j ∧ L.j≤f ∧ L.j=(books (ρ i)).stock.j ∧
         L.arm=((books (ρ i)).rows (d i)).arm false (homogeneous F Jr Z (ρ i).val (d i).val (x i)) ∧
         ∀N per K,L.j<N→f≤K→
           variation R (fun i=>(d i).val) L.j N per i (L.arm.source (N,per))≤M i*(β K)^(E i):=by
  obtain ⟨price,e,hp,cash⟩:=WilsonMovingForkHomeIncome.original F Jr Z simple bliss slow lead paid D T h d x books window
  obtain ⟨onset,columns⟩:=eventually_atTop.mp (WilsonReflectedOpticalStock.columns R simple slow)
  let overhead(i:Fin n):=2*orbitCost ((C).labels.level (d i).val)*allowance R (d i).val
  have pos(i:Fin n):0≤overhead i:=mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans (orbitCost_one_le _)))
    (zero_le_one.trans (WilsonOriginalObservedRosePooledWrap.positive R (d i).val))
  refine ⟨fun i=>overhead i*price i,fun i=>e i+1,fun i=>mul_nonneg (pos i) (zero_le_one.trans (hp i)),?_⟩
  intro gate
  filter_upwards [cash,WilsonMovingForkSlotDate.original F simple bliss slow D T h (max gate onset) d books] with r wages dates
  intro ρ span near f i L
  let v(t:Fin n):=homogeneous F Jr Z (ρ t).val (d t).val (x t)
  have dt:=dates ρ span near v i
  have file:=WilsonMovingForkSlotDate.source F (books (ρ i)) (d i) (v i)
  have fb:1≤β f:=((P).fits.delayed f).le
  refine ⟨(le_max_left ..).trans dt.1,dt.2.1,file.1,file.2,?_⟩
  intro N per K live before
  have inc:=WilsonReflectedOpticalStock.monotone R simple
  have wage:=wages ρ span near (fun _=>false) i
  have stock:((P).params L.j).columns≤β K:=(columns L.j ((le_max_right ..).trans dt.1)).trans (inc (dt.2.1.trans before))
  let fee:=WilsonReflectedPublicStationFare.fee F ((books (ρ i)).rows (d i)) false (v i)
  have source:Next.UVStress.quota (C) (d i).val L.j N per (L.arm.source (N,per))≤a L.j^(d i).val*fee:=L.numerical N per live
  have amount:fee≤price i*(β K)^(e i):=wage.2.1.trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans fb) (inc before) _) (zero_le_one.trans (hp i)))
  calc
    _≤overhead i*β K*fee:=WilsonOriginalObservedRosePooledWrap.original R (fun i=>(d i).val) i L.j N per K _ (cap _) stock source
    _≤overhead i*β K*(price i*(β K)^(e i)):=mul_le_mul_of_nonneg_left amount
      (mul_nonneg (pos i) (zero_le_one.trans ((P).fits.delayed K).le))
    _=_:=by rw [pow_succ];ring

end YM.Integration.WilsonOriginalObservedRosePooledPurse
end
