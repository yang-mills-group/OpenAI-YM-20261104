import YM.Integration.WilsonIndependentMovingRosterAllFineRead
import YM.Integration.WilsonIndependentMovingRosterSector

/-! The full fine-cut comparison for a finite near roster and a distant
field, read on their common older Mer law. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterAllFine
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterCut (residual)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonIndependentMovingRosterBirthCalendar (room)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open scoped BigOperators Topology Classical

variable {G:Gauge}{n:ℕ}

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(F:SealR G)(k e u target:ℕ)(positive:0<target)
    (E W V Sn Dn Do:Credit):
    let a:=F.h+(u+target)
    let b:=capP Q+F.h+(u+target+2)
    ∃first shape chron:Credit,∀(R:Realm G (e+1) E)(_fresh:SpringD R k u b W)(_outer:SpringD R k u a W)
      (_inner:SpringD R (capP Q) (u+a) (capP Q+(u+a+2)) Sn)(_dorm:Dormitory R (capP Q) (u+a) Dn)
      (_end:Dormitory R (F.h+capP Q) u Do)(_roster:HorizonP H R W V Q)(_far:PassportC H R F W V)
      (older t m N:ℕ)(_gate:R.anchor ≤ older)(_start:older ≤ t)(_home:t ≤ m)(_top:m ≤ N)(_capacity:F.h+capP Q ≤ k)
      (φ:Wilt Q)(ψ:Rarity F.D)(X:Herit Q)(Y:F.Rider)(o:CellR)(y r inner outer DF:ℝ)(B:Fin (n+1)→ℝ),
      let T:=paceT R.draws.S m t
      let Z:=epoch R older m
      let fresh:=WilsonSeparatedPrefixMovingUnformedSector.invoice Q F X Y e k u b r outer DF B
      let formed:=shape.buy (room r inner y)*WilsonIndependentMovingRosterInvoice.charge Q F X Y e u a r outer DF B
      let price:=2*fresh*first.buy Z+4*formed*chron.buy Z
      0 < inner → 0 < outer → (∀s,Amplitude (φ s) (B s)) → Amplitude ψ DF →
      (∀s b,s≠b→ClearDay (φ s) (φ b) inner) →
      (∀s,∀p∈tsupport (φ s).ψ.val,∀z∈tsupport ψ.ψ.val,T*outer ≤ dist p (T • z)) →
      (∀z∈tsupport ψ.ψ.val,T*outer+1+|y| ≤ ‖T • z‖) →
      (∀s,(φ s).radius+|y|+1 ≤ r) → ψ.radius+|y/T|+1 ≤ r → 2+2*|y| ≤ r →
      ∀ω:Fin 0→YForest G,Heard e target T price (fun q=>(residual R Q F φ ψ X Y o y t m older N).2 q 0 ω):=by
  intro a b
  obtain ⟨first,plain⟩:=WilsonSeparatedPrefixMovingUnformedSector.original H Q F k e u target E W V Do
  obtain ⟨shape,chron,old⟩:=WilsonIndependentMovingRosterSector.original H Q F k e u target positive E W V Sn Dn Do
  refine ⟨first,shape,chron,?_⟩
  intro R freshSpring outerSpring innerSpring dorm terminal roster far older t m N gate start home top capacity
    φ ψ X Y o y r inner outer DF B T Z fresh formed price inside outside amps amp pair separated remote nbox fbox cbox ω
  have allFresh:=plain R freshSpring terminal roster far older t m N gate start home top capacity
    φ ψ X Y o y outer r DF B outside amps amp separated nbox fbox
  have fit (s): (φ s).radius ≤ r:=by linarith only [nbox s,abs_nonneg y]
  have allFormed:=old R outerSpring innerSpring dorm terminal roster far older t m N gate start home top capacity
    φ ψ X Y o y r inner outer r DF B inside outside amps amp fit pair remote cbox fbox
  apply WilsonIndependentMovingRosterAllFineRead.original R Q F roster far φ ψ X Y o y t m older N target ω
    (gate.trans start) home (start.trans home) top (2*fresh*first.buy Z) (4*formed*chron.buy Z)
  · intro q hq
    refine (allFresh q hq ω).trans_eq ?_
    change 2*((T^target)⁻¹*fresh)*first.buy Z=(T^target)⁻¹*(2*fresh*first.buy Z)
    ring
  · intro q hq
    refine (allFormed q hq ω).trans_eq ?_
    change 4*((T^target)⁻¹*formed)*chron.buy Z=(T^target)⁻¹*(4*formed*chron.buy Z)
    ring

/-- A single radial condition at the actual far test suffices on a bounded
near housing. Both clearances use the real supports on this board. -/
theorem separated {Q:Fin (n+1)→SealR G}(φ:Wilt Q){d:ℕ}(ψ:Rarity d)(T outer r y:ℝ)
    (fits:∀s,(φ s).radius+|y|+1 ≤ r)(remote:∀z∈tsupport ψ.ψ.val,T*outer+r ≤ ‖T • z‖)
    (center:2+2*|y| ≤ r):
    (∀s,∀p∈tsupport (φ s).ψ.val,∀z∈tsupport ψ.ψ.val,T*outer ≤ dist p (T • z)) ∧
    (∀z∈tsupport ψ.ψ.val,T*outer+1+|y| ≤ ‖T • z‖):=by
  constructor
  · intro s p hp z hz
    have near:=Metric.mem_closedBall.mp ((φ s).support hp)
    have tri:=dist_triangle (0:Point4) p (T • z)
    rw [dist_zero_left,dist_comm (0:Point4) p] at tri
    linarith only [near,tri,remote z hz,fits s,abs_nonneg y]
  · intro z hz
    linarith only [center,abs_nonneg y,remote z hz]

end YM.Integration.WilsonIndependentMovingRosterAllFine
