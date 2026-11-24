import YM.Integration.WilsonSeparatedPrefixMovingPinDay
import YM.Integration.WilsonSeparatedPrefixMovingNextCalendar

/-! The sum over both true fine contact dates has a single older-age
credit and a fixed power of the ratio to the exterior scale. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonSeparatedPrefixMovingPinSector
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile WilsonSeparatedPrefixMovingCalendar
open WilsonSeparatedPrefixMovingPairSector (current vacant)
open WilsonIndependentMovingRosterRejoin (stored)
open WilsonSeparatedPrefixMovingFineFare (unitFee)
open WilsonSeparatedPrefixMovingPinController (Sites)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(k e u target:ℕ)(pos:0 < target)
    (E W V Sn Dn Do:Credit):
    let a:=F.h+(u+target)
    ∃shape chron:Credit,∀(R:Realm G (e+1) E)(canvas:Sites G e u)(_per:SpringD R k u a W)
      (_near:SpringD R (capP Q) (u+a) (capP Q+(u+a+2)) Sn)(_dorm:Dormitory R (capP Q) (u+a) Dn)
      (_terminal:Dormitory R (F.h+capP Q) u Do)(_roster:HorizonP H R W V Q)(_far:PassportC H R F W V)
      (older t m N:ℕ)(_gate:R.anchor ≤ older)(_read:older ≤ t)(_home:t ≤ m)(_top:m ≤ N)(_capacity:F.h+capP Q ≤ k)(φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)
      (o:CellR)(y rad inner outer v DF:ℝ)(B:Fin (n+1)→ℝ),
      let T:=paceT R.draws.S m t
      let ticket:=shape.buy (WilsonIndependentMovingRosterBirthCalendar.room rad inner y)*
        WilsonIndependentMovingRosterInvoice.charge Q F X Y e u a v outer DF B
      0 < inner → 0 < outer → (∀s,Amplitude (φ s) (B s)) → Amplitude ψ DF → (∀s,(φ s).radius ≤ rad) →
      (∀s b,s≠b→ClearDay (φ s) (φ b) inner) →
      (∀p∈tsupport ψ.ψ.val,T*outer+1+|y| ≤ ‖T • p‖) → 2+2*|y| ≤ v → ψ.radius+|y/T|+1 ≤ v →
      ∀q ≤ e,∀ω:Fin 0→YForest G,
        ‖∑d∈Finset.range (N-m),∑l∈(Finset.range (N-m)).filter (fun l=>d ≤ l),
          WilsonSeparatedPrefixMovingPinDay.crossed R canvas Q F φ ψ X Y o y t m older N q ω (m+d) (m+l)‖ ≤
          4*((T^target)⁻¹*ticket)*chron.buy (epoch R older m):=by
  intro a
  obtain ⟨C,D,each⟩:=WilsonSeparatedPrefixMovingPinDay.original H Q F k e u target pos E W V Sn Dn Do
  refine ⟨C,D.finances 1 le_rfl,?_⟩
  intro R canvas per near dorm terminal roster far older t m N gate read home top capacity φ ψ X Y o y rad inner outer
    v DF B T ticket innPos outPos amps ampf fits apart away box fbox q hq ω
  have om:=read.trans home
  have gpos:1 ≤ WilsonIndependentMovingRosterBirthCalendar.room rad inner y:=le_max_left ..
  have vr:0 ≤ v:=by linarith only [box,abs_nonneg y]
  have paid:0 ≤ ticket:=mul_nonneg (zero_le_one.trans (C.purchase gpos))
    (WilsonIndependentMovingRosterInvoice.positive Q F X Y e u a v outer DF B vr outPos ampf.1 (fun s=>(amps s).1))
  have nonneg:0 ≤ (T^target)⁻¹*ticket:=mul_nonneg (inv_nonneg.mpr (pow_nonneg (pace_pos ..).le _)) paid
  apply WilsonSeparatedPrefixMovingNextCalendar.original R D older m (N-m) gate om _ nonneg
  intro d hd l hl order
  have fine:=Finset.mem_range.mp hl
  by_cases past:m+d < m+l
  · exact each R canvas per near dorm terminal roster far older t m (m+d) (m+l) N gate read home (by omega) past
      (by omega) capacity φ ψ X Y o y rad inner outer v DF B innPos outPos amps ampf fits apart away box fbox q hq ω
  · rw [WilsonSeparatedPrefixMovingPinDay.crossed,if_neg past,norm_zero]
    have creditPos:=zero_le_one.trans (D.purchase (window R older m (m+l+1) gate om (by omega)).1)
    exact mul_nonneg (mul_nonneg nonneg creditPos) (mul_nonneg (pace_pos ..).le (sq_nonneg _))

end YM.Integration.WilsonSeparatedPrefixMovingPinSector
