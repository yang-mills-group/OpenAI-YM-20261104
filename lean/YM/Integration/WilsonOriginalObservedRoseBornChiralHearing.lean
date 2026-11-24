import YM.Integration.WilsonOriginalObservedRoseBornChiralExcess
import YM.Integration.WilsonOriginalObservedRoseBornChiralProducts
import YM.Integration.WilsonOriginalObservedRoseBornChiralProper

/-! The two reflected ears in their native detector-then-upper order, using any already elected compact bulb. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornChiralHearing
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

open WilsonOriginalObservedRoseBornChiralProper (submitted atGrade stableFee fittedFee)
open WilsonOriginalObservedRoseBornChiralProducts (centered)
open WilsonIndependentMatchedFittedSeat (receiving)

def first (V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(m K N:ℕ)
    (y:ℝ)(o:CellR)(ω:Fin 0→YForest G):ℝ:=
  centered (atGrade (cruises V.draws V.paid N (capP Q) K m (ordinary V.draws X φ m K y o)) 1 ω)
    (fun q=>atGrade (submitted (X 0) (φ 0) y o) q ω) (fun q=>atGrade (submitted (X 1) (φ 1) y o) q ω)

def projected (V:Realm G (e+1) J)(X:Courts (H:=H) (v:=v))(φ:Wilt Q)(m K N:ℕ)
    (y:ℝ)(o:CellR)(ω:Fin 0→YForest G):ℝ:=
  centered (atGrade (stopped V.draws V.paid Q φ (fun i=>home (Q i) (X i)) m K N m y o) 1 ω)
    (fun q=>atGrade (receiving (X 0) 1 (φ 0) y o 0) q ω)
    (fun q=>atGrade (receiving (X 1) 1 (φ 1) y o 0) q ω)

theorem original (M:Master H)(Q:Fin 2→SealR G)(cap:capP Q=10)(v:∀i,Rails (Q i).h k u₀ e)
    (height seats gain:ℕ)(surplus:2≤gain)(stage:2*k≤10+gain)(room:10+gain ≤ seats)(width:10+gain≤u₀)(heat:1≤e):
    ∃primary basal unary:Fin 2→Credit,∃terminal:(Fin 2→Bool)→Credit,
    ∀(V:Realm G (e+1) J),Elected M V height seats → ∀(X:Courts (H:=H) (v:=v))
    (m K N:ℕ),stamp V X m K N → V.anchor ≤ m → m ≤ K → K ≤ N → (∀i,On (Q i).h (X i).pt) →
    ∀(φ:Wilt Q)(fees:Fin 2→ℝ)(y space:ℝ),Bough Q φ y space fees → ∀(o:CellR)(ω:Fin 0→YForest G),
    let S:=fun i=>stableFee (X i) (unary i) (φ i) (fees i) y
    let F:=fun i=>fittedFee (X i) (φ i) (fees i) y
    ‖first V X φ m K N y o ω-projected V X φ m K N y o ω‖ ≤
      (∑j∈Finset.univ.erase (WilsonIndependentMatchedRosterMasks.quiet 1),(wage gain V X φ fees y space primary terminal m (choose 1 j)+
      bill (10+gain) V m K X basal (fun i=>dose (X i) 1) (choose 1 j) (radius φ y) fees))+
      2*(S 0*(S 1+F 1)+F 0*S 1):=by
  obtain ⟨primary,basal,terminal,pair⟩:=WilsonOriginalObservedRoseBornChiralExcess.original
    M Q cap v height seats gain surplus stage room width
  choose unary paid using (fun i=>WilsonOriginalObservedRoseBornChiralProper.original H (Q i).ans (Q i).path (v i) J J J J)
  refine ⟨primary,basal,unary,terminal,?_⟩
  intro V sold X m K N stamp₀ floor past live sound φ fees y space grant o ω S F
  let A (i:Fin 2)(q:ℕ):=atGrade (submitted (X i) (φ i) y o) q ω
  let B (i:Fin 2)(q:ℕ):=atGrade (receiving (X i) 1 (φ i) y o 0) q ω
  have measured (i:Fin 2)(q:ℕ)(limit:q≤1):‖A i q-B i q‖ ≤ S i ∧ ‖B i q‖ ≤ F i:=
    (paid i (X i) (φ i) (fees i) y o (sound i) (grant.lanes i) q (limit.trans heat) ω).2
  have all:=pair V sold X m K N stamp₀ floor past live sound φ fees y space grant o 1 heat ω
  let joint:=atGrade (cruises V.draws V.paid N (capP Q) K m (ordinary V.draws X φ m K y o)) 1 ω
  let bank:=atGrade (stopped V.draws V.paid Q φ (fun i=>home (Q i) (X i)) m K N m y o) 1 ω
  have paid₀:=WilsonOriginalObservedRoseBornChiralProducts.original joint bank (A 0) (A 1) (B 0) (B 1)
    (S 0) (S 1) (F 0) (F 1) (measured 0) (measured 1)
  exact paid₀.2.trans (add_le_add all le_rfl)

end YM.Integration.WilsonOriginalObservedRoseBornChiralHearing
