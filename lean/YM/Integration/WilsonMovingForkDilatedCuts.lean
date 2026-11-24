import YM.Integration.WilsonMovingForkStencilCutoffRows
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.WilsonMovingForkDilatedCuts
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext PhysicalNext.Repeat.Legato
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open RG05Readout Next.Rank Next.Rank.Station
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFourSquare
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonMovingForkHeterogeneousCut (Invoice Filed Heard)
open WilsonMovingForkMixedSeed (doses product)
open WilsonThermometerUnitFilingFlatTelescope WilsonOriginalTwoFlatTelescope
open WilsonPublicForkTrialHearing
open scoped Classical Topology BigOperators
open WilsonMovingForkDatedExterior (At)
open WilsonMovingForkShiftedSite (Reached)

open WilsonMovingForkPrintedFile (Program row)

variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  {l:Ultrafilter (ℕ×ℕ)} {j K:ℕ}{I:Type}[Fintype I]
  (m:I→ℕ)(d:(s:I)→Fin (m s)→ℕ)(fields:∀s i,S.Field (d s i))
  (acquired:∀s i,Arm R.family S (l:Filter _) (d s i) (fields s i))
  (actual:∀s,Fin (m s)→ Cover)(μ:I→ℂ)
local notation "C" => R.family

include F in
/-- An original and a separately regulated grouped scalar meet only after the signed cell sum. -/
theorem original (order:(l:Filter _)≤f.fuse)(jK:j≤K)(clear:∀s,tag ((C).S.a j) (actual s)∈generic (m s))
    (stopped grouped:I→(ℕ×ℕ)→ℂ)(cash:I→(ℕ×ℕ)→ℝ)(cross endFee:(ℕ×ℕ)→ℝ)(room:ℝ)
    (earned:∀ᶠz:ℕ×ℕ in f.fuse,∀top:K<z.1,∀s,‖(C).omega z.1 z.2
       (word R (d s) j z.1 z.2 (jK.trans top.le) (actual s) (fun i=>(acquired s i).source z))-
       stopped s z‖≤cash s z)
    (matched:∀ᶠz:ℕ×ℕ in f.fuse,‖∑s,μ s*(stopped s z-grouped s z)‖≤cross z)
    (fitted:∀ᶠz:ℕ×ℕ in f.fuse,‖∑s,μ s*grouped s z‖≤endFee z)
    (spent:∀ᶠz:ℕ×ℕ in f.fuse,(∑s,‖μ s‖*cash s z)+cross z+endFee z≤room):
    ‖∑s,μ s*S.classMoment S (d s) (tag ((C).S.a j) (actual s)) (fields s)‖≤room:=by
  let Y:=fun s (z:ℕ×ℕ)=>(C).ensemble (d s)
    (fun i=>if h:j≤z.1 then ((C).S.toDepth h z.2).embed (wrap _ (actual s i)) else 0)
    (fun i=>(acquired s i).source z)
  have land:=fun s=>WilsonReflectedPublicAlignedPoints.aligned F order j (actual s) (clear s)
    (generic_conf _ (clear s)) (acquired s)
  have approach:=tendsto_finsetSum Finset.univ (fun s _=>(tendsto_const_nhds (x:=μ s)).mul (land s))
  apply le_of_tendsto approach.norm
  have late:∀ᶠz:ℕ×ℕ in f.fuse,K<z.1:=by
    rw [Order.fused];exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_gt_atTop K
  filter_upwards [earned.filter_mono order,matched.filter_mono order,fitted.filter_mono order,spent.filter_mono order,late.filter_mono order] with z native align last pay live
  have top:K<z.1:=live
  have fees:‖(∑s,μ s*Y s z)-∑s,μ s*stopped s z‖≤∑s,‖μ s‖*cash s z:=by
    rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro s _
    rw [←mul_sub,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simp only [Y,dif_pos (jK.trans top.le)]
    exact native top s
  have gap:‖(∑s,μ s*stopped s z)-∑s,μ s*grouped s z‖≤cross z:=by
    simpa only [mul_sub,Finset.sum_sub_distrib] using align
  have each:‖∑s,μ s*Y s z‖≤
      ‖(∑s,μ s*Y s z)-∑s,μ s*stopped s z‖+
        (‖(∑s,μ s*stopped s z)-∑s,μ s*grouped s z‖+‖∑s,μ s*grouped s z‖):=by
    calc
      _ ≤ ‖(∑s,μ s*Y s z)-∑s,μ s*stopped s z‖+‖∑s,μ s*stopped s z‖:=by
        simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (∑s,μ s*Y s z) (∑s,μ s*stopped s z) 0
      _ ≤ _:=add_le_add le_rfl (by simpa only [sub_zero] using
        norm_sub_le_norm_sub_add_norm_sub (∑s,μ s*stopped s z) (∑s,μ s*grouped s z) 0)
  exact each.trans ((add_le_add fees (add_le_add gap last)).trans (by simpa only [add_assoc] using pay))

end YM.Integration.WilsonMovingForkDilatedCuts
end
