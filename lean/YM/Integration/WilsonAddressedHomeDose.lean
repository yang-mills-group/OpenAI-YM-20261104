import YM.Integration.WilsonAddressedMixedHomeTrial
import YM.Integration.WilsonReflectedMixedThermalArms
import YM.Integration.WilsonReflectedPublicCommonDose
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonAddressedHomeDose
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
local notation "meshSize" => R.family.S.a
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



open WilsonAddressedMixedStationRange (width)
open WilsonMeasuredPublicEntranceGridDebit (fitted bill settled)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedPublicSignedFare (amplitude)
open WilsonAddressedPublicGuardFare (word)
open OPE.Therm (Poetry)



open WilsonAddressedMixedEnrolledTrial (Funded)
open WilsonMovingForkWindowBooks (Priced)
open WilsonPositionHomogeneousFrame (homogeneous)

open WilsonReflectedMixedThermalArms (rent)
open WilsonReflectedPublicCommonDose (dose)
set_option warningAsError true
set_option maxHeartbeats 850000

def ceiling (d:ℕ)(cash:ℝ):ℝ:=max (2*cash) (rent R d cash)

omit [Fintype I] [DecidableEq I] [Nonempty I] in
theorem filed {D T:ℕ}(d:I → Fin (D+1))(x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(r:{r:ℝ // 0<r ∧ r<δ}) → WilsonOriginalTwoFlatPublicBooks.Book F (l:=l) H z D T r.val)
    (ρ:I → {r:ℝ // 0<r ∧ r<δ})(M:I → ℝ)(E:I → ℕ)(one:∀i,1 ≤ M i)
    (f N per:ℕ)(deep:f<N)(ref:∀e ≤ D,(C).ref e ≤ N)
    (upper:∀i,(ρ i).val ≤ 1)
    (homes:∀i b,WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) b ≤ f)
    (fare:∀i b,let v:=homogeneous F Jr Z (ρ i).val (d i).val (x i)
      WilsonOriginalTwoFlatPublicFare.charge F ((books (ρ i)).rows (d i)) f b v ≤ M i*(β f)^(E i))
    (V:(e:Fin (D+1)) → Sight C e.val per)(u:(e:Fin (D+1)) → Emblems C e.val)
    (est:∀e:Fin (D+1),Opened C e.val f per)
    (enrolled:∀e,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per e.val
      (digits R N per 0) (V e) (u e))
    {J:Type}[DecidableEq J](pick:J → I)(branch:J → Bool)(s:Finset J):
    let v:=fun i=>homogeneous F Jr Z (ρ i).val (d i).val (x i)
    let raw:=fun j=>(((books (ρ (pick j))).rows (d (pick j))).arm (branch j) (v (pick j))).source (N,per)
    let χ:=fun j=>WilsonThermometerMarchSource.charge (offer R (raw j) (est (d (pick j))) deep.le)
    (∏j∈s,(ρ (pick j)).val^(d (pick j)).val/dose (χ j) (rent R (d (pick j)).val (M (pick j))) 1) ≤ 
    (∏j∈s,ceiling (R:=R) (d (pick j)).val (M (pick j)))*(β f)^(∑j∈s,E (pick j)):=by
  classical
  intro v raw χ
  have hp:1 ≤ β f:=((P).fits.delayed f).le
  have bounds(j:J):
      (ρ (pick j)).val^(d (pick j)).val/dose (χ j) (rent R (d (pick j)).val (M (pick j))) 1 ≤ 
      ceiling (R:=R) (d (pick j)).val (M (pick j))*(β f)^(E (pick j)):=by
    let i:=pick j
    let L:=(books (ρ i)).rows (d i)
    have original:=WilsonAddressedAlignedColumn.original R (enrolled (d i)) deep.le (le_refl f)
      (fun e he=>ref e (he.trans (Nat.le_of_lt_succ (d i).isLt))) (est (d i)) (raw j)
    have stock:=WilsonOriginalTwoFlatPublicFare.issued F L (books (ρ i)).checked (branch j) (v i)
      (p:=per) (homes i (branch j)) deep
    have salary:size (offer R (raw j) (est (d i)) deep.le) ≤ 2*(M i*(β f)^(E i)) :=
      original.2.trans (mul_le_mul_of_nonneg_left (stock.trans (fare i (branch j))) zero_le_two)
    let bound:=ceiling (R:=R) (d i).val (M i)*(β f)^(E i)
    have base:1 ≤ (β f)^(E i):=one_le_pow₀ hp
    have inCash:2*M i ≤ ceiling (R:=R) (d i).val (M i):=le_max_left .. 
    have positive:1 ≤ ceiling (R:=R) (d i).val (M i):=(show 1 ≤ 2*M i by linarith [one i]).trans inCash
    have small:1 ≤ bound:=one_le_mul_of_one_le_of_one_le positive base
    have booked:χ j ≤ bound:=by
      refine max_le small (salary.trans ?_)
      rw [←mul_assoc]
      exact mul_le_mul_of_nonneg_right inCash (zero_le_one.trans base)
    have rentBound:rent R (d i).val (M i) ≤ bound:=calc
      _ ≤ ceiling (R:=R) (d i).val (M i):=le_max_right ..
      _ ≤ _:=le_mul_of_one_le_right (zero_le_one.trans positive) base
    have denom:WilsonReflectedPublicCommonDose.denominator (χ j) (rent R (d i).val (M i)) 1 ≤ bound:=by
      change max (max 1 (χ j)) (rent R (d i).val (M i)*1) ≤ bound
      exact max_le (max_le small booked) (by simpa only [mul_one] using rentBound)
    have radius:(ρ i).val^(d i).val ≤ 1:=pow_le_one₀ (ρ i).property.1.le (upper i)
    rw [div_eq_mul_inv,WilsonReflectedPublicCommonDose.refund]
    exact (mul_le_of_le_one_left (zero_le_one.trans ((le_max_left (1:ℝ) (χ j)).trans (le_max_left ..))) radius).trans denom
  rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun j _=>div_nonneg (pow_nonneg (ρ (pick j)).property.1.le _)
    (WilsonReflectedPublicCommonDose.positive ..).le) (fun j _=>bounds j)

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (D T h:ℕ)(d:I → Fin (D+1))(x:∀i,RG17.Free C (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ}) → WilsonOriginalTwoFlatPublicBooks.Book F (l:=l) H z D T s.val)
    (window:∀s,Priced F (books s)):
    ∃M:I → ℝ,∃E:I → ℕ,(∀i,1 ≤ M i) ∧ ∀ᶠr in trail,∀ρ:I → {s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) → 
      let m:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 m
      ∀N per(deep:f<N)(V:(e:Fin (D+1)) → Sight C e.val per)(u:(e:Fin (D+1)) → Emblems C e.val)
      (est:∀e:Fin (D+1),Opened C e.val f per),
      (∀e,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N per e.val
        (digits R N per 0) (V e) (u e)) → 
      ∀(J:Type)[DecidableEq J](pick:J → I)(branch:J → Bool)(s:Finset J),
      let v:=fun i=>homogeneous F Jr Z (ρ i).val (d i).val (x i)
      let raw:=fun j=>(((books (ρ (pick j))).rows (d (pick j))).arm (branch j) (v (pick j))).source (N,per)
      let χ:=fun j=>WilsonThermometerMarchSource.charge (offer R (raw j) (est (d (pick j))) deep.le)
      (∏j∈s,(ρ (pick j)).val^(d (pick j)).val/dose (χ j) (rent R (d (pick j)).val (M (pick j))) 1) ≤ 
        (∏j∈s,ceiling (R:=R) (d (pick j)).val (M (pick j)))*(β f)^(∑j∈s,E (pick j)):=by
  classical
  obtain ⟨M,E,first,earned⟩:=WilsonMovingForkHomeIncome.original F Jr Z simple bliss slow lead paid D T h d x books window
  refine ⟨M,E,first,?_⟩
  let bound:=univ.sup (fun q:Fin (D+1)=>(C).ref q.val)
  filter_upwards [earned,WilsonAddressedMixedStationRange.original F simple bliss slow D T h bound d books,
    (longer F simple bliss h).eventually ((gt_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds)]
    with r grant range within
  intro ρ span near m f N per deep V u est enrolled J _ pick branch s
  have funds:=grant ρ span near
  obtain ⟨past,rooms⟩:=range ρ span near
  have sharp(e:ℕ)(he:e ≤ D):(C).ref e ≤ N:=by
    let q:Fin (D+1):=⟨e,Nat.lt_succ_of_le he⟩
    exact (Finset.le_sup (f:=fun j:Fin (D+1)=>(C).ref j.val) (mem_univ q)).trans (past.trans deep.le)
  exact filed F Jr Z d x books ρ M E first f N per deep sharp
    (fun i=>(span i).2.trans within.le) (fun i b=>(rooms i b).2.1) (fun i b=>(funds (fun _=>b) i).2.2)
    V u est enrolled pick branch s

end YM.Integration.WilsonAddressedHomeDose
end
