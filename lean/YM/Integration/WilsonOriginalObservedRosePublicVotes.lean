import YM.Integration.WilsonOriginalObservedRosePublicWages
import YM.Integration.WilsonOriginalObservedRoseVaneTop

/-! The cutoff-independent gross price of the previously booked weak physical Rose on its published public board. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePublicVotes
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

open WilsonOriginalObservedRoseVanePurse (ages)
open WilsonOriginalObservedRoseMeshHeight (variation)
open WilsonOriginalMicroscopicGuardedPage (wrapCost)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)
open WilsonOlderFreshSoftSocketStationPair (amount)
open WilsonOriginalObservedRoseMeshHeight (tilt height)
open WilsonOriginalObservedRoseScaledWallet (share)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonThermometerDeclaredSeeds
local notation "J" => Stock.census (Fin 3)

def width (e:Fin 3→ℕ):ℕ:=Finset.univ.sup (fun i=>e i+1)

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(lead:Leading F Jr)
    (obedient:∀d:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) d)
    (slow:WilsonWindowReportingPace.Slow R.kit)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (cap:∀j,1≤((P).budget j).supportExponent)(upper:∀j,((P).budget j).supportExponent≤100)
    (quote:OPE.Therm.Poetry (P)):
    ∃(M:Fin 3→ℝ)(D:ℕ),(∀i,0≤M i) ∧ ∀m:ℕ,∀ᶠr in trail,∀{T:ℕ}(B:Book F (l:=l) H z 6 T r),
    WilsonMovingForkWindowBooks.Priced F B → ∀_actual:Next.UVStress.Lifts (C) B.k,
    ∀(N per b K requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N →
    ∀(panel:Panel R ages N per b K bk kn requested power tag credit)(file:Filed R ages K),
    panel.slot=file.station → panel.axis=file.A N per → (∀i,panel.slot i=B.W.k) →
    (∀i,panel.names i=((B.rows (grade i)).arm true (homogeneous F Jr Z r (grade i) (source C univ i))).source (N,per)) →
    ∀s:(J).Mode,∀z':ℝ,1≤z' → (a B.W.k)/(a K)≤z'^m → r/(a K)≤z'^m →
    let w:=votes R ages (N:=N) (per:=per) file panel.names panel.turn
    r^(height ages s.val)*(∑q:Selection R ages s.val,‖weight R ages N per K w s.val q‖)≤
      wallet R ages M s.val*(β K)^D*z'^(m*height ages s.val+1):=by
  obtain ⟨M,e,m0,earned⟩:=WilsonOriginalObservedRosePublicWages.original F Jr Z simple bliss lead obedient slow shop cap upper quote
  refine ⟨M,width e*3,m0,?_⟩
  intro m
  have positive:0<tilt 3 m:=by unfold WilsonOriginalObservedRoseMeshHeight.tilt;positivity
  obtain ⟨L,fitted⟩:=WilsonOriginalObservedRoseMeshPurse.original R ages simple shop cap positive
  have radius:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  filter_upwards [earned,radius,(ge_mem_nhds ((C).S.a_pos L)).filter_mono nhdsWithin_le_nhds] with r wage rp tiny
  intro T B booked actual N per b K requested power tag credit bk kn deep panel file stations axes homes names s z' large age top w
  have mesh:a B.W.k≤r:=(WilsonReflectedPublicBulbBerth.mesh R B.W B.checked).trans B.active.le
  have late:L≤B.W.k:=by
    by_contra! early
    exact (not_le_of_gt ((C).S.strictAnti early)) (mesh.trans tiny)
  have before:B.W.k≤b:=homes 0 ▸ panel.before 0
  have bought:=fitted N per b K bk kn requested power tag credit panel file stations axes (fun i=>homes i ▸ late) deep
  have met:1≤β K:=((P).fits.delayed K).le
  have wages:=wage B booked actual N per K (before.trans_lt deep) (before.trans bk)
  have funds(i:Fin 3):0≤M i*(β K)^width e:=mul_nonneg (m0 i) (pow_nonneg (zero_le_one.trans met) _)
  have fee(i:Fin 3):r^(ages i)*((C).labels.level (ages i)).coeffSize (w i)≤
      (M i*(β K)^width e)*z'^(m*ages i)*share 3 z':=by
    have bill:=bought.1 i
    have origin:panel.names i=WilsonNeutralOffsetCutoff.named R (group F Jr Z B actual) N per i:=
      (names i).trans ((B.rows (grade i)).weak _ _)
    rw [homes i,origin] at bill
    apply WilsonOriginalObservedRoseScaledWallet.columns R ages m B.W.k K N per i _ _ rp large age top bill
    apply (wages i).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ met (Finset.le_sup (f:=fun j=>e j+1) (Finset.mem_univ i))) (m0 i)
  have total:=WilsonOriginalObservedRoseScaledWallet.original R ages N per K m kn w s.val (fun i=>M i*(β K)^width e) rp large funds (fun i _=>fee i)
  rw [WilsonOriginalObservedRoseVaneTop.wallet_scale] at total
  have card:Fintype.card s.val≤3:=by simpa only [Fintype.card_coe,Fintype.card_fin] using Finset.card_le_univ s.val
  have cost:0≤wallet R ages M s.val:=Finset.prod_nonneg fun i _=>mul_nonneg (Finset.sum_nonneg fun q _=>WilsonReceivedCanonicalVersePortfolio.nonneg R ages i q) (m0 i)
  apply total.trans
  rw [←pow_mul]
  gcongr

end YM.Integration.WilsonOriginalObservedRosePublicVotes
end
