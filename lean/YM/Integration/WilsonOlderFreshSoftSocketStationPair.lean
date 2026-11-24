import YM.Integration.WilsonOriginalTwoFlatRoseBook
import YM.Integration.WilsonMovingForkWeakPrice
import YM.Integration.WilsonOlderFreshSoftSocketStationBook

/-! The guarded receipt on the exact original Rose station and its previously appointed physical vectors. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationPair
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

local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatRoseBook (group)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalMicroscopicGuardedGridSchool (Finished)
open WilsonOlderFreshSoftRoseMesh (filed)
open WilsonPositionThermometerGradedSource
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations
open WilsonReflectedPublicStationFare
open PhysMS
open MS MS.Land FVA2 FVA2.Register
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse

variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)

def amount {r:ℝ}{T:ℕ}(B:Book F (l:=l) H z 6 T r)(i:Fin 3):ℝ:=
  (a B.W.k)^(grade i).val * fee F (B.rows (grade i)) true
    (homogeneous F Jr Z r (grade i) (source (C) univ i))

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(cap:∀j,1≤((P).budget j).supportExponent)
    (quote:OPE.Therm.Poetry (P)):
    ∃(C₀:Fin 3→ℝ)(e:Fin 3→ℕ),(∀i,1≤C₀ i) ∧ ∀(order:ℕ){η:ℝ},0<η→∀ᶠr in trail,∀{T:ℕ}(B:Book F (l:=l) H z 6 T r),
    WilsonMovingForkWindowBooks.Priced F B→∀(actual:Next.UVStress.Lifts (C) B.k),
    Finished R (fun i=>(grade i).val) (fun _=>B.W.k) order η (amount F Jr Z B) (filed R (group F Jr Z B actual)) ∧
    (∀i,0≤amount F Jr Z B i) ∧ ∀K,B.W.k≤K→∀i,amount F Jr Z B i≤C₀ i*(β K)^(e i):=by
  have quota(i:Fin 3):=WilsonMovingForkWeakPrice.original F Jr Z simple bliss lead obedient (grade i).val (source (C) univ i)
  choose C₀ e C₁ sale using quota
  refine ⟨C₀,e,C₁,?_⟩
  intro order η ep
  obtain ⟨floor,guard⟩:=WilsonOriginalMicroscopicGuardedDated.original R simple shop cap quote (fun i=>(grade i).val) order ep
  filter_upwards [Filter.eventually_all.mpr sale,(ge_mem_nhds ((C).S.a_pos floor)).filter_mono nhdsWithin_le_nhds,
    (ge_mem_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with r old tiny unit
  intro T B bought actual
  have mesh:a B.W.k≤r:=(WilsonReflectedPublicBulbBerth.mesh R B.W B.checked).trans B.active.le
  have late:floor≤B.W.k:=by
    by_contra! earlier
    exact (not_le_of_gt ((C).S.strictAnti earlier)) (mesh.trans tiny)
  let v i:=homogeneous F Jr Z r (grade i) (source (C) univ i)
  have paid(i:Fin 3):=WilsonReflectedPublicStationFare.original F (B.rows (grade i)) B.checked true (v i)
  have bounded (i:Fin 3)(N per:ℕ)(live:B.W.k<N):
      Next.UVStress.quota (C) (grade i).val B.W.k N per (filed R (group F Jr Z B actual) i (N,per))≤amount F Jr Z B i:=by
    have h:=(paid i).2 N per live
    rw [(B.rows (grade i)).weak] at h
    exact h
  have pos i:0≤amount F Jr Z B i:=by
    apply le_trans _ (bounded i (B.W.k+1) 0 (Nat.lt_succ_self _))
    unfold Next.UVStress.quota Frame.coeffSize
    exact Finset.sum_nonneg fun _ _=>norm_nonneg _
  refine ⟨guard (fun _=>B.W.k) (fun _=>late) (amount F Jr Z B) (filed R (group F Jr Z B actual)) bounded,pos,?_⟩
  intro K after i
  have due:=old i (B.rows (grade i)) B.checked B.active (bought (grade i)) K after
  have g1:(a B.W.k)^(grade i).val≤1:=pow_le_one₀ ((C).S.a_pos _).le (mesh.trans unit)
  have g0:0≤(a B.W.k)^(grade i).val:=pow_nonneg ((C).S.a_pos _).le _
  change (a B.W.k)^(grade i).val*fee F (B.rows (grade i)) true (v i)≤_
  have rhs0:0≤C₀ i*(β K)^(e i):=mul_nonneg (zero_le_one.trans (C₁ i)) (pow_nonneg (zero_le_one.trans ((P).fits.delayed K).le) _)
  calc
    _≤(a B.W.k)^(grade i).val*(C₀ i*(β K)^(e i)):=mul_le_mul_of_nonneg_left due g0
    _≤1*(C₀ i*(β K)^(e i)):=mul_le_mul_of_nonneg_right g1 rhs0
    _=_:=one_mul _

end YM.Integration.WilsonOlderFreshSoftSocketStationPair
end
