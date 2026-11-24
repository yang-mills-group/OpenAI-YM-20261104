import YM.WilsonCoeffUV.Emit.ReportingClocks
/-!
# Window charges and Λ, opening costs in actual β̂ convention

Registers Λ=2+log β̂ exactly. ζ := zz = 1+log log. Target uses any fixed polynomial
in Λ, with ρ lower Λ^20 reduced here for formal high pass ONLY. No real mask tests.
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Layout
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{A:Levels G}{E W:Credit}{m b j e a:ℕ}{R:Realm G e E}{r:ℝ}
lemma pace_fewer (S:Schedule)(m b:ℕ) : paceT S m b=paceT S m (b+1)*(S.block b).val:= by rw [← pace_step]
lemma block_pay (p:R.anchor ≤ j)(t:j≤ m)(f:R.y=zz R.draws): ((R.draws.S.block j).val:ℝ)≤ E.buy (zz R.draws m):=(R.taxes j p).height.trans (E.elder (R.depth j p) (by rw [f]; exact short_mono _ R.hG t))
lemma disCC (p:Windows R.draws a m b j r)(v:R.anchor≤ b)(x:0≤r)(T:Credit) (t:r ≤ T.buy (longLog R.draws m))(f:R.y=zz R.draws): paceT R.draws.S m b ≤ (T.prodC E).buy (longLog R.draws m) :=by
    rw [pace_fewer, Credit.products]; have hz:1≤ zz R.draws m:=by rw [← f]; exact R.depth m (v.trans p.capture.le)
    exact mul_le_mul (p.lastC.le.trans t) ((block_pay v p.capture.le f).trans (E.elder hz (tiny_log ..))) (by positivity) (x.trans t)
-- proof log log limiter. T arbitrary
lemma log_denom (P:Credit): ∃ A:Credit,∀ z x:ℝ, z≥1→x=2+Real.exp (z-1)→ Real.log (P.buy x) ≤ A.buy z:=by
    let T:=(Credit.leanC.plus (pur (Real.log 3))).prodC (pur P.d); let U:= T.plus (pur (Real.log P.x)); have hp:0<P.x:= zero_lt_one.trans_le P.good
    refine ⟨U,fun z x hx hz=>?_⟩; have h:2≤x:=by rw [hz]; linarith only [Real.exp_pos (z-1)]
    have hq : Real.log x≤ Real.log 3 + z:=by
        have h' := (show 1 ≤ Real.exp z from Real.one_le_exp (by linarith)); have he:x≤3*Real.exp z:=by rw [hz]; linarith [Real.exp_le_exp.mpr (show z-1≤z by linarith)]
        exact (Real.log_le_log (by linarith) he).trans_eq (by rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp])
    unfold Credit.buy; rw [Real.log_mul hp.ne' (by positivity),Real.log_pow]; rw [add_comm]; apply le_trans _ (Credit.fuel _ _ hx); refine add_le_add ?_ (pure_goal ..); rw [Credit.products]; have hZ: P.d*Real.log x ≤ ((Credit.leanC.plus (pur (Real.log 3))).buy z)*P.d:=by
        rw [mul_comm (P.d:ℝ)]; have hy: Real.log x ≤ _:= hq.trans (le_trans (show Real.log 3+z≤ Credit.leanC.buy z+ (pur (Real.log 3)).buy z from by linarith only [Credit.lean_cost z, pure_goal (Real.log 3) z]) (Credit.fuel _ _ hx))
        exact mul_le_mul_of_nonneg_right hy (by positivity)
    exact hZ.trans (mul_le_mul_of_nonneg_left (pure_goal ..) (zero_le_one.trans (Credit.purchase _ hx)))
lemma compar_top (_p:R.anchor ≤ j)(v:j≤ m)(f:R.y=zz R.draws): Compar R.draws.S R.y j m ≤ zz R.draws m+2*snowP R.draws.S j m:=by unfold Compar; rw [f]; have hh:= winterH R.draws.S v; unfold snowP at *; linarith only [short_mono R.draws R.hG v, hh]
lemma soft_cost (P E:Credit):∃ B U:Credit,∀ (R:Realm G e E) a m b j r, Windows R.draws a m b j r → R.anchor ≤ j → 1≤r → r ≤ P.buy (longLog R.draws m) → R.y=zz R.draws →
    Compar R.draws.S R.y j m ≤ B.buy (longLog R.draws m)∧ PadRank R b m (U.buy (zz R.draws m)) ∧ snowP R.draws.S b m ≤ U.buy (zz R.draws m) :=by
   obtain ⟨T,h⟩:= log_denom (P.prodC E); let U:= T.plus T |>.plus Credit.leanC; let X:=U.plus (Credit.leanC.powC 2 |>.plus E); let B:= X.plus X |>.plus Credit.leanC
   refine ⟨B,U,fun R a m b j r p v u y t=>?_⟩; let S:=R.draws; let z':= zz S m; let Z:= longLog S m; have hm:j≤ m:=p.soft.le.trans p.capture.le; have hz:1≤z':=by unfold z' S; rw [← t]; exact R.depth m (v.trans hm)
   have hZ:z'≤Z:=tiny_log ..
   have he: snowP S.S b m ≤ T.buy z':=(pact S.S m b) ▸ le_trans (Real.log_le_log (pace_pos ..) (disCC p (v.trans p.soft.le) (zero_le_one.trans u) P y t)) (h z' Z hz (by unfold Z longLog z'; rw [spend]))
   have hU: 2*T.buy z'+z'≤U.buy z':= le_trans (by linarith only [Credit.fuel T T hz, Credit.lean_cost z']) (Credit.fuel (T.plus T) Credit.leanC hz)
   have hb: Compar S.S R.y b m≤ U.buy z':= by linarith only [show _≤z'+2*snowP S.S b m from compar_top (v.trans p.soft.le) p.capture.le t,he,hU]
   have hV: snowP S.S b m≤ U.buy Z:=by have H:= U.elder hz hZ; linarith only [he, hU,hz,H,T.purchase hz]
   have hX: snowP S.S j b ≤ (Credit.leanC.powC 2 |>.plus E).buy Z:=by
       have hx: snowP S.S (j+1) b ≤ Z^2:= p.lastS.le.trans (pow_le_pow_left₀ (by linarith [long_pos S b]) (monolog S R.hG p.capture.le) _)
       have hy: Real.log ((S.S.block j).val) ≤ E.buy Z:=le_trans (by linarith [Real.log_le_sub_one_of_pos (show 0 < ((S.S.block j).val:ℝ) by positivity)]) ((block_pay v hm t).trans (E.elder hz hZ))
       apply le_trans _ (Credit.fuel _ E (hz.trans hZ)); rw [Credit.power,Credit.lean_cost]; unfold snowP at *; linarith only [S.S.scale_succ j,hx,hy]
   have h':snowP S.S j m ≤ X.buy Z:=by apply le_trans _ (Credit.fuel U _ (hz.trans hZ)); unfold snowP at *; linarith only [hX,hV]
   have hy:= PadRank.frugal R (v.trans p.soft.le) p.capture.le
   constructor
   · have hx:= Credit.fuel (X.plus X) Credit.leanC (hz.trans hZ); rw [Credit.lean_cost] at hx; change _ ≤ B.buy Z; unfold B; linarith only [show _≤z'+2*snowP S.S j m from compar_top v hm t,hZ,h',hx,Credit.fuel X X (hz.trans hZ)]
   exact ⟨⟨fun i p v=> (hy.year i p v).trans hb,hy.lengthS.trans hb⟩,by change snowP S.S b m ≤ _; exact he.trans (by linarith only [hU,hz,T.purchase hz])⟩
end YM.WilsonCoeffUV.Layout
