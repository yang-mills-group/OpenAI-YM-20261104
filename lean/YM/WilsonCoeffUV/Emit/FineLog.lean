import YM.WilsonCoeffUV.Emit.LayoutOpening
/-!
# One possible top choice and sold ultraviolet release

Top depends on m. Overlap stability uses only the common formal expansion convention
with true power δ by mesh. Exhibits a choice between Λ and Λ² costing flat
at Λ^C reserves. Uses linear y supply (general windows separately).
-/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.WilsonCoeffUV.Layout
open Wheel.ScaleS Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost Physical
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Wheel.Flooring Ticket
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{S:Schedule}{V W:Credit}{m N e n:ℕ}{R:Realm G (e+1) Credit.leanC}
lemma coarse_fine (R:Realm G e Credit.leanC)(p:R.anchor≤ m)(h:m≤ N): snowP R.draws.S m (N+1) ≤2*snowP R.draws.S m N+R.y m:=by
   let S:= R.draws.S; have Hx:(↑(S.block N).val:ℝ) ≤ R.y N:=by
       have hv:= (R.taxes N (p.trans h)).height; change (↑(S.block N).val:ℝ)≤ Credit.leanC.buy (R.y N) at hv; rwa [Credit.lean_cost] at hv
   have ht:= R.age m N p h; have he:= S.scale_succ N; have hz:= Real.log_le_sub_one_of_pos (show 0 < ((S.block N).val:ℝ) by positivity); unfold S at *; unfold snowP; linarith
lemma take_finer (S:Schedule)(m:ℕ)(X:ℝ)(p:0<X):∃ n:ℕ,m ≤ n∧ snowP S m n ≤ X ∧ X ≤ snowP S m (n+1):=by
    classical
    obtain ⟨a,h⟩:= exists_nat_gt X
    have ht:∃ n:ℕ,m≤ n∧X ≤ snowP S m n:=by
        refine ⟨m+a,Nat.le_add_right ..,?_⟩; apply le_trans h.le; simpa only [Nat.add_sub_cancel_left] using winterH S (show m≤ m+a by omega)
    let n:= Nat.find ht; obtain ⟨hn,hx⟩:= (Nat.find_spec ht); change m≤ n at hn; change X≤ snowP S m n at hx; have hz: n≠m:= fun h=> not_le_of_gt p ((h ▸ hx : X ≤ snowP S m m).trans_eq (sub_self _)); let b:= n-1; have hb:n=b+1:=by omega
    have hf:= Nat.find_min ht (show b<n by omega); refine ⟨b,(by omega),lt_of_not_ge (fun p=> hf ⟨(by omega),p⟩) |>.le,?_⟩; exact hb ▸ hx

def fineLength (A: Levels G)(m:ℕ):ℝ:=longLog A m*Real.sqrt (longLog A m)
lemma fineLength_ok (A:Levels G)(m:ℕ): longLog A m≤ fineLength A m:= le_mul_of_one_le_right (by linarith [long_pos A m]) (Real.one_le_sqrt.mpr (by linarith [long_pos A m]))
lemma cutoff (R:Realm G e Credit.leanC)(p:R.y=zz R.draws)(t:R.anchor≤ m):∃ N:ℕ,m ≤ N ∧ fineLength R.draws m≤ snowP R.draws.S m N ∧ snowP R.draws.S m N ≤ 3*fineLength R.draws m:=by
    have hp:=long_pos R.draws m; let K:= fineLength R.draws m; have he:longLog R.draws m ≤ K:=fineLength_ok ..; obtain ⟨n,hn,h,h'⟩:= take_finer R.draws.S m K (by linarith)
    refine ⟨n+1,(by omega),h', le_trans (coarse_fine R t hn) ?_⟩; rw [p]; linarith [tiny_log R.draws m]
lemma UVsaves (T:Credit)(A: Levels G)(g:G.Simple)(q:ℝ)(h:q>0): ∀ᶠ m in atTop,∀ N:ℕ,fineLength A m ≤ snowP A.S m N → T.buy (longLog A m)*trailC A.S m N≤ Real.exp (-(q*longLog A m)):=by
   obtain ⟨P,f⟩:= log_denom T
   filter_upwards [exempt A g P (c:=1) (by norm_num), (toward A g).eventually_ge_atTop ((4*(1+q))^2), (stamp_lim A g).eventually_ge_atTop 1] with m hm he hu; intro N x; let Z:=longLog A m; have hZ: 1≤Z:=by linarith [long_pos A m]
   have hl:Real.log (T.buy Z)≤ Z:=le_trans (f (zz A m) Z hu (by rw [spend]; rfl)) (hm.trans (le_of_eq (one_mul _))); have hx:T.buy Z>0:= zero_lt_one.trans_le (T.purchase hZ); refine ((Real.log_le_iff_le_exp (mul_pos hx (trail_pos ..))).mp ?_)
   rw [Real.log_mul hx.ne' (trail_pos ..).ne',trailC, Real.log_exp]
   have hg:= (Real.le_sqrt (by positivity) (zero_le_one.trans hZ)).mpr he
   unfold snowP at x; nlinarith only [mul_le_mul_of_nonneg_left hg (zero_le_one.trans hZ),hl,x, show fineLength A m = Z*Real.sqrt Z from rfl]
end YM.WilsonCoeffUV.Layout
