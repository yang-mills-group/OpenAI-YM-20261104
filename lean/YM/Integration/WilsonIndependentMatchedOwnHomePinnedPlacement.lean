import YM.Integration.WilsonIndependentMatchedOwnHomeProfile
import YM.Integration.WilsonSeparatedPrefixMovingGroupedShift

/-! Move the actual K pin onto every compact derivative test in the common
near ruler. The entire placed group field is unchanged after this reindexing. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomePinnedPlacement
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMatchedCoverProfile (word)
open scoped BigOperators Topology Classical
variable {G:Gauge}{D n:ℕ}

theorem support (f:Phrase D)(v:Point4):tsupport (WilsonIndependentFittedExteriorProfile.shift f v).val ⊆
    (fun x=> -v+x) ⁻¹' (tsupport f.val):=by
  apply closure_minimal _ (isClosed_closure.preimage (continuous_const.add continuous_id))
  intro x hx
  exact subset_closure hx

def moved (φ:Rarity D)(v:Point4):Rarity D where
  ψ:=WilsonIndependentFittedExteriorProfile.shift φ.ψ v
  radius:=‖v‖+φ.radius
  markG:=le_trans φ.markG (by linarith only [norm_nonneg v])
  support:=by
    intro x hx
    have bound:=φ.support (support φ.ψ v hx)
    rw [Metric.mem_closedBall,dist_zero_right] at bound ⊢
    calc ‖x‖=‖v+(-v+x)‖:=by rw [add_neg_cancel_left]
         _≤‖v‖+‖-v+x‖:=norm_add_le _ _
         _≤_:=add_le_add_right bound _

theorem wheel (φ:Rarity D)(x y:ℝ)(v s:Cover)(o:CellR):
    wheelC x y (s+v) (moved φ (x • actualW s)).ψ o = wheelC x y v φ.ψ o:=by
  apply Subtype.ext
  funext w
  apply ContinuousMap.ext;intro c
  change crease (sonal _ _ _ _ _) w.2 c.val=crease (sonal _ _ _ _ _) w.2 c.val
  have hj:=Nat.le_of_lt_succ w.1.isLt
  rw [currentP _ _ _ _ _ _ hj,currentP _ _ _ _ _ _ hj]
  change _*crease (WilsonIndependentFittedExteriorProfile.shift _ _) _ _=_
  rw [WilsonIndependentFittedExteriorProfile.shifted]
  congr 2
  unfold Mer.address Mer.position
  rw [Mer.actual_plus,smul_add]
  abel

theorem original (P:TowerS G D)(φ:Rarity D)(x y:ℝ)(pos:0<x)(o:CellR)(s:Cover)(h:ℕ):
    shifted (word P φ x y o h) s=word P (moved φ (x • actualW s)) x y o h:=by
  let f:=moved φ (x • actualW s)
  have rotated (a:Cover):shoe P f x y (s+a)=shifted (shoe P φ x y a) s:=by
    let w₀:=wheelC x y a φ.ψ
    have w:wheelC x y (s+a) f.ψ=w₀:=ContinuousMap.ext fun z=>wheel φ x y a s z
    unfold shoe
    rw [w,shifted_add]
  have active (a:Cover):a∈VisitsT φ x y o ↔ s+a∈VisitsT f x y o:=by
    rw [visiting pos,visiting pos,wheel]
  unfold word
  rw [pupil_eye _ _ _ _ _ _ pos,pupil_eye _ _ _ _ _ _ pos,WilsonCoeffUV.Wheel.Motion.shiftedSum]
  apply Finset.sum_bij (fun a _=>s+a) (fun a ha=>(active a).mp ha) (fun _ _ _ _ hit=>add_left_cancel hit)
  · intro b hb
    refine ⟨-s+b,(active _).mpr ?_,by abel⟩
    simpa only [add_neg_cancel_left] using hb
  · intro a _
    change shifted (drumB h x • locale o (shoe P φ x y a)) s=drumB h x • locale o (shoe P f x y (s+a))
    rw [rotated]; rfl

theorem pin (S:Schedule)(m c K:ℕ)(before:c ≤ K)(site:Cover):
    paceT S m K • actualW (WilsonPositionProgramPinnedHearthHistory.pin S c K site)=paceT S m c • actualW site:=by
  induction before with
  | refl=>simp [WilsonPositionProgramPinnedHearthHistory.pin,WilsonPositionProgramPinnedHearthHistory.count]
  | @step i old ih=>
    rw [WilsonPositionProgramPinnedHearthHistory.moves S old site,actual_mult,smul_smul,pace_step,ih]

end YM.Integration.WilsonIndependentMatchedOwnHomePinnedPlacement
end
