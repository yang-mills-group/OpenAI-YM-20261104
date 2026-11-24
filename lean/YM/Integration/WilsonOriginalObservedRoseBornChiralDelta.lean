import YM.Integration.WilsonOriginalObservedRoseBornChiralRetained

/-! The two reflected ears in their native detector-then-upper order, using any already elected compact bulb. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralDelta
open YM.WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonIndependentMatchedRosterLane WilsonIndependentMatchedCoverPairBudget
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedRosterSlots (entry wallet degree count)
open WilsonIndependentMatchedPhysicalComponent (volume price)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedRosterPlanted (response)
open WilsonIndependentMatchedPhysicalMasks (ranksV)
open WilsonSeparatedPrefixMovingReportedLanes (Courts row amount)
open WilsonSeparatedPrefixMovingReportedStableEdge (tuition)
open WilsonSeparatedPrefixMovingReportedStableLaw (reading)
open WilsonIndependentMatchedPhysicalSector (stamp)
open WilsonIndependentMovingRosterAllFineSeats (Elected)
open WilsonSeparatedPrefixMovingCalendar (epoch)

open WilsonSeparatedPrefixMovingReportedFaculty (sector)
open Trace Trace.Pilot FVA2 FVA2.Register Spec Extraction OPE PhysicalNext.Repeat.Legato
open Maxwell Maxwell.Free XSpace XSpace.Cirrus XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Photo
open WilsonMaxwellThermometerReflectedIncidence Table.Pairing
open WilsonMaxwellThermometerPublicStation (aperture)
open WilsonMaxwellThermometerSignedWallet (board)
open WilsonPhysicalChiralPairReading (Paid)
open WilsonPositionProgramReflectedPurse (shape)
open MS MS.WilsonBridge.Coupling
variable {G:Gauge}{k e u₀:ℕ}{H:Hol G}
local notation "J" => Credit.leanC


open WilsonIndependentMatchedBufferedVacuum (stopped)
open WilsonOriginalObservedRoseBornChiralEars (radius)
open WilsonIndependentMatchedRosterMasks (Bits choose quiet)
open WilsonIndependentMatchedPhysicalReturn (ordinary)
open WilsonPositionProgramTrialAccrued (home)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentMatchedPhysicalSector (field)
open private summed from YM.Integration.WilsonIndependentMatchedRosterPlanted

variable {Q:Fin 2→SealR G}{v:∀i,Rails (Q i).h k u₀ e}

open WilsonOriginalObservedRoseBornChiralRankHome (bill)
open WilsonOriginalObservedRoseBornChiralRankOffice (wage)

open WilsonSeparatedPrefixMovingRetainedFaculty (quarter)
open WilsonOriginalObservedRoseBornChiralRetained (charge)

def portfolio (gain:ℕ)(V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ)
    (primary basal:Fin 2→Credit)(terminal:(Fin 2→Bool)→Credit)(m:ℕ):ℝ:=
  ∑s∈Finset.univ.erase (WilsonIndependentMatchedRosterMasks.quiet 1),
    charge gain V X φ fees y space primary basal terminal m (choose 1 s)

theorem original (M:Master H)(Q:Fin 2→SealR G)(cap:capP Q=10)
    (v:∀i,Rails (Q i).h k u₀ e)(height seats gain:ℕ)(surplus:2 ≤ gain)(stage:2*k ≤ 10+gain)
    (room:10+gain ≤ seats)(width:10+gain ≤ u₀)
    :
    ∃primary basal:Fin 2→Credit,∃terminal:(Fin 2→Bool)→Credit,
      ∀(V:Realm G (e+1) J),Elected M V height seats → ∀(X:Courts (H:=H) (v:=v))
      (m K N:ℕ),stamp V X m K N → V.anchor ≤ m → m ≤ K → K ≤ N →
      (∀i,On (Q i).h (X i).pt) → ∀(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ),
      Bough Q φ y space fees → ∀(o:CellR)(q:ℕ),q ≤ e → ∀ω:Fin 0→YForest G,
      ‖(cruises V.draws V.paid N (capP Q) K m (ordinary V.draws X φ m K y o)-
        stopped V.draws V.paid Q φ (fun i=>home (Q i) (X i)) m K N m y o).2 q 0 ω‖ ≤
      (paceT V.draws.S m K)^(1/4:ℝ)*portfolio gain V X φ fees y space primary basal terminal m:=by
  obtain ⟨primary,basal,terminal,pay⟩:=WilsonOriginalObservedRoseBornChiralRetained.original M Q cap v
    height seats gain surplus stage room width
  refine ⟨primary,basal,terminal,?_⟩
  intro V sold X m K N chart start past live sound φ fees y space book o q hq ω
  have rows:=WilsonIndependentMatchedPhysicalReturn.exactRows V X φ fees m m K N y o chart le_rfl past live sound book.lanes
  rw [rows]
  simp only [←WilsonOriginalObservedRoseBornChiralRank.at_upper V X m K N chart,Prod.snd_sum,Finset.sum_apply]
  apply (norm_sum_le _ _).trans
  unfold portfolio
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j costly
  let flag:=choose 1 j
  have estimate:=pay V sold X m K N chart start past live sound φ fees y space book flag o q hq ω
  have w:(1/4:ℝ)≤quarter flag:=WilsonOriginalObservedRoseBornChiralRetained.holds j (Finset.mem_erase.mp costly).1
  have dp:=pace_pos V.draws.S m K
  have cc:0≤charge gain V X φ fees y space primary basal terminal m flag:=by
    by_contra! bad
    exact (not_lt_of_ge ((norm_nonneg _).trans estimate)) (mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos dp _) bad)
  exact estimate.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge dp (pace_le _ past) w) cc)

end YM.Integration.WilsonOriginalObservedRoseBornChiralDelta
