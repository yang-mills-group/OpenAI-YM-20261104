import YM.Integration.WilsonOriginalObservedRoseBornChiralMasked
import YM.Integration.WilsonSeparatedPrefixMovingRetainedFaculty

/-! The payable contribution of each of the four actual marked/unmarked binary inputs at the earlier report. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralRetained
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
open WilsonIndependentMatchedRosterTariff (factor)
def charge (gain:ℕ)(V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ)
    (primary basal:Fin 2→Credit)(terminal:(Fin 2→Bool)→Credit)(m:ℕ)(flag:Fin 2→Bool):ℝ:=
  let c:=fun i=>dose (X i) 1
  let z:=radius φ y
  let b:=10+gain
  2*(terminal flag).buy (epoch V m m)*tuition b e b space⁻¹ z (amount 0 b primary X c flag) fees+
    coinMat (ranksV flag k fun i=>(Q i).h) e*(∏i:Fin 2,factor 0 b z*(fees i*amount 0 b basal X c flag i))

theorem upper (flag:Fin 2→Bool):quarter flag≤1/2:=by
  rw [quarter,Fin.sum_univ_two]
  cases h:flag 0 <;> cases h':flag 1 <;> norm_num [WilsonIndependentMatchedRosterSlots.count,h,h']

theorem holds (s:Bits 1)(marked:s≠WilsonIndependentMatchedRosterMasks.quiet 1):1/4≤quarter (choose 1 s):=by
  obtain ⟨i,marked_at⟩:=WilsonIndependentMatchedRosterMasks.present 1 s marked
  have h:=Finset.single_le_sum (f:=fun j:Fin 2=>count (choose 1 s j)) (fun j _=>Nat.zero_le _) (Finset.mem_univ i)
  rw [marked_at] at h
  have h':(1:ℝ)≤((∑j:Fin 2,count (choose 1 s j):ℕ):ℝ):=by exact_mod_cast h
  unfold quarter
  linarith

theorem original (M:Master H)(Q:Fin 2→SealR G)(cap:capP Q=10)
    (v:∀i,Rails (Q i).h k u₀ e)(height seats gain:ℕ)(surplus:2 ≤ gain)(stage:2*k ≤ 10+gain)
    (room:10+gain ≤ seats)(width:10+gain ≤ u₀)
    :
    ∃primary basal:Fin 2→Credit,∃terminal:(Fin 2→Bool)→Credit,
      ∀(V:Realm G (e+1) J),Elected M V height seats → ∀(X:Courts (H:=H) (v:=v))
      (m K N:ℕ),stamp V X m K N → V.anchor ≤ m → m ≤ K → K ≤ N →
      (∀i,On (Q i).h (X i).pt) → ∀(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ),
      Bough Q φ y space fees → ∀(flag:Fin 2→Bool)(o:CellR)(q:ℕ),q ≤ e → ∀ω:Fin 0→YForest G,
      ‖(sector V flag X (fun i=>dose (X i) 1) φ y o m K N).2 q 0 ω‖ ≤
        (paceT V.draws.S m K)^(quarter flag)*charge gain V X φ fees y space primary basal terminal m flag:=by
  obtain ⟨primary,terminal,edges⟩:=WilsonSeparatedPrefixMovingRetainedFaculty.original
    (n:=0) M Q v (10+gain) gain height seats (by simpa using stage) (by omega) (by omega) (by omega)
  obtain ⟨basal,homebound⟩:=WilsonOriginalObservedRoseBornChiralRankHome.original (H:=H) Q v (10+gain) width
  refine ⟨primary,basal,terminal,?_⟩
  intro V sold X m K N filed floor past live sound φ fees y space book flag o q qa ω
  have radial (i:Fin 2):radiusH (φ i) 1 y ≤ radius φ y:=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _=>abs_nonneg (radiusH (φ j) 1 y)) (Finset.mem_univ i))
  have positive:0<space⁻¹:=inv_pos.mpr (lt_of_lt_of_le zero_lt_one book.pos)
  let c:=fun i=>dose (X i) 1
  let upper:=sector V flag X c φ y o m K N
  let lower:=sector V flag X c φ y o m m N
  have g:(2:ℝ)≤gain:=by exact_mod_cast surplus
  have exponent:3/2≤(gain:ℝ)-quarter flag:=by linarith [WilsonOriginalObservedRoseBornChiralRetained.upper flag]
  have between:=((edges V sold X m m K N filed floor le_rfl past live φ fees y
    (radius φ y) space⁻¹ o positive book.seats radial book.lanes c flag exponent).2.2 q qa ω)
  simp only [cap,pace_self,Real.one_rpow,mul_one] at between
  have initial:=(homebound V X m K N filed φ fees y space book c flag o).2 q qa ω
  calc
    ‖upper.2 q 0 ω‖ = ‖((upper-lower)+lower).2 q 0 ω‖ := by rw [sub_add_cancel]
    _ ≤ ‖(upper-lower).2 q 0 ω‖+‖lower.2 q 0 ω‖ := norm_add_le _ _
    _ ≤ _ := (add_le_add between initial).trans_eq (by dsimp only [charge,bill,quarter];ring)

end YM.Integration.WilsonOriginalObservedRoseBornChiralRetained
