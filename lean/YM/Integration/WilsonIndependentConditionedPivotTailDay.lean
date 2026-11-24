import YM.Integration.WilsonIndependentConditionedPivotTailLaw

/-! One upper first join, returned to its actual older field. After the one
local spatial purchase the complete deposited field travels in moment zero. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailDay
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMovingRosterBirth (charge)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonIndependentConditionedPivotTailLaw (deposit)
open scoped BigOperators Topology Classical
variable {G:Gauge}{n:ℕ}

theorem original (H:Hol G)(Q:Fin (n+1)→SealR G)(e gain:ℕ)(E W V S U:Credit):
    ∃C:Credit,∀(R:Realm G (e+1) E),HorizonP H R W V Q →
      SpringD R (capP Q) 0 (capP Q+gain) S → Dormitory R (capP Q) 0 U →
      ∀(host m j N:ℕ),R.anchor ≤ host → host ≤ m → m ≤ j → j<N →
      ∀(φ:Wilt Q)(X:Herit Q)(B:Fin (n+1)→ℝ)(y room:ℝ)(o:CellR),Bough Q φ y room B →
        let Y:=deposit Q R φ X host m j N y o
        let wages:=C.buy (epoch R host (j+1))*(paceT R.draws.S m (j+1))^gain*
          (C.buy room*charge Q X e B)
        Auth (capP Q) Y ∧ Flush e 0 1 Y wages:=by
  obtain ⟨source,first⟩:=WilsonIndependentMovingRosterBirth.original H Q E W V S e 0 gain
  obtain ⟨receiver,send⟩:=waveSeen G (capP Q) e 0 E U
  let C:=receiver.prodC source
  refine ⟨C,?_⟩
  intro R paid spring old host m j N opening stops dates top φ X B y room o geo Y wages
  let clock:=epoch R host (j+1)
  let Z:=max room clock
  let w:=paceT R.draws.S m (j+1)
  let D:=Ash R.draws R.paid φ X m j N y o
  have endUp:=window R host m (j+1) opening stops (dates.trans (Nat.le_succ j))
  have endDown:=window R host host (j+1) opening le_rfl (stops.trans (dates.trans (Nat.le_succ j)))
  have clockFit:clock ≤ Z:=le_max_right .. 
  have ears:=first R paid (by simpa only [Nat.zero_add] using spring) m j N φ X B Z y o (opening.trans stops) dates top
    (endUp.2.2.1.trans clockFit) (boughRise geo (le_max_left ..))
  have pad:PadRank R host j Z:=by
    refine ⟨fun t th tj=>(endDown.2.2.2.year t th (tj.trans (Nat.le_succ j))).trans clockFit,?_⟩
    exact (Nat.cast_le.mpr (Nat.sub_le_sub_right (Nat.le_succ j) host)).trans
      (endDown.2.2.2.lengthS.trans clockFit)
  have escort:Escort R host j (fun _=>1):=by
    refine ⟨opening,stops.trans dates,fun _ _ _=>zero_le_one,fun _ _ _=>le_rfl,?_⟩
    intro t _ _
    exact div_le_self zero_le_one (by exact_mod_cast (R.draws.S.block t).pos)
  have received:=send R old host j (fun _=>1) j N N _ (max 0 (R.tempC j j)) Z escort pad le_rfl top.le top.le
    (le_max_right _ _) D D (Fringed.same ears.2.2 ears.1 (le_max_left _ _))
  have entry:Flush e 0 1 Y (C.buy Z*w^gain*charge Q X e B):=by
    dsimp only [C]
    rw [Credit.products,mul_assoc (receiver.buy Z),mul_assoc (receiver.buy Z)]
    exact received.f_l
  have room0:1 ≤ room:=geo.pos
  have clock0:1 ≤ clock:=endUp.1
  have comparison:C.buy Z ≤ C.buy clock*C.buy room:=by
    rcases le_total room clock with lo|hi
    · rw [show Z=clock from max_eq_right lo]
      exact le_mul_of_one_le_right (zero_le_one.trans (C.purchase clock0)) (C.purchase room0)
    · rw [show Z=room from max_eq_left hi]
      exact le_mul_of_one_le_left (zero_le_one.trans (C.purchase room0)) (C.purchase clock0)
  have coins:0 ≤ charge Q X e B:=by
    apply Finset.prod_nonneg
    intro s _
    apply mul_nonneg (geo.lanes s).1
    unfold WilsonSeparatedPrefixMovingOwnDate.fee
    positivity
  have whole:C.buy Z*w^gain*charge Q X e B ≤ wages:=by
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right comparison (pow_nonneg (pace_pos ..).le _)) coins).trans_eq
    dsimp only [wages,clock,w]
    ring
  exact ⟨received.pen,entry.1.trans whole,fun k hk l hl=>(entry.2 k hk l hl).more whole⟩

end YM.Integration.WilsonIndependentConditionedPivotTailDay

