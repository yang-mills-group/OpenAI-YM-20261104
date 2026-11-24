import YM.MSbar.Alto.Atlas
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Alto
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}
open Supply Input
variable {O:ChartRatio G}{K:MapPrices} {B: Sheet G}{D: Rolls B}{Θ:Protection D}{T:Delays Θ}{W: Bar T}{I:Wait W}{P:PostCost D}(A:Directed G I O K P)
local notation "B₀"=> A.kin
local notation "ℓ"=> A.a
set_option quotPrecheck false
local notation "ω'"=>A.a.clock
-- payment consistent with Legato.Delays.Any.Start.stages feasible. use win certified.Adj.
variable (s p k:ℕ)(t x:ℝ)
noncomputable def countV (G:Gauge)(L:Side)(x:ℝ) := x+G.slopeConstant*Real.log L.val
noncomputable def flurry (w:ℝ) := Real.log w^2
noncomputable def cWidth (t:ℝ):=1/(flurry t)^2
structure Request (K:MapPrices)(O:ChartRatio G)(A:Stage)(j i:ℕ)(V:KernelChoices)(F:Patch)(s p:ℕ)(x:ℝ): Prop where
    E0 : let y:=countV G F.L x; let L:=F.L; let b:=cWidth x; let b':=cWidth y; let w:=flurry x; let w':=flurry y
         ∃ t:Uniform.Before G A.width A.paths j V (p+3), let a:=grain A.clip F t (K.α j); let B:= Alto.tango K j i s p F O t a (t.tables A.clip F)
            Ready B G Dean L s p b w w' ∧ b ≤ ceilα K j i ∧ b' ≤ K.α j/2 ∧ b/L.val ≤ b' ∧ b/L.val ≤ a
variable (g:G.Simple)
variable (J:MapPrices)(j i:ℕ)(α:ChartRatio G)(B:Stage)(X:Patch){Q:KernelChoices}
include g
noncomputable abbrev grainPos (X:Patch)(α':ℝ)(B:Stage)(T:Uniform.Before G B.width B.paths j Q p) := 0 < Parma.grain B.clip X T α'
-- positive tables even no bind.L from shape.L.Profile. `rate` positivity.T.cons.inspect zeroGap.Allows before. 
lemma roundT (T:Uniform.Before G B.width B.paths j Q (p+3))(hh:X.J=j):0 < Parma.grain B.clip X T (J.α j):= by
    -- may require Gap using Tables.tilt from allCost positive absolute etc Before.shell
    let V:=T.tables B.clip X; let d:=J.α j; have ht:=J.alpha_pos j
    have hp:0 < V.gap:=by exact Uniform.zeroGap_pos .. -- uses Harness Parameters
    have hx:0 < V.width:=by
        unfold V Uniform.Before.tables; dsimp only; exact div_pos (width_positive B.width_pos _ _) (by positivity)
    have h0:0 ≤ V.value:= by unfold V Uniform.Before.tables allCost; positivity
    have he:0 < V.rate:= tiltWidth_pos _ (half_pos hp) hx h0; unfold grain; change _< min V.rate _/5; positivity
lemma drift_scale (L: Side): ∀ᶠ x:ℝ in atTop, 1 ≤ flurry x ∧ flurry x ≤ flurry (countV G L x) ∧ flurry (countV G L x) ≤ 1.1 * flurry x:=by
   let c:= G.slopeConstant*Real.log L.val; have he:c≥0:=mul_nonneg (slopeConstant_pos g).le (Real.log_nonneg (Nat.one_le_cast.mpr L.property)); filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (100*Real.log 2 +1), eventually_ge_atTop c,eventually_gt_atTop (1:ℝ)] with x hx ht hv
   have hp:1 ≤ Real.log x:= le_trans (by have he:0≤Real.log 2:=Real.log_nonneg one_le_two; linarith only [he]) hx
   have hz:countV G L x=x+c:=rfl; rw [hz]; unfold flurry; have hx':0<x:=by linarith only [hv]
   refine ⟨one_le_pow₀ hp, pow_le_pow_left₀ (zero_le_one.trans hp) (Real.log_le_log hx' (by linarith only [he])) _,?_ ⟩
   have ht: Real.log (x+c) ≤ Real.log x*1.02:=by
       have hh := Real.log_le_log (show 0<x+c by linarith only [hx',he]) (show x+c ≤ x*(2:ℝ) by linarith only [ht]); rw [Real.log_mul hx'.ne' (by norm_num)] at hh; linarith only [hx,hp,hh]
   nlinarith only [pow_le_pow_left₀ (show 0≤Real.log (x+c) from Real.log_nonneg (by linarith only [he,hv])) ht 2,sq_nonneg (Real.log x)]
omit g in
lemma broad : Tendsto flurry atTop atTop:= (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp Real.tendsto_log_atTop
lemma billU (L:Side) : Tendsto (fun x=> flurry (countV G L x)) atTop atTop:=tendsto_atTop_mono' atTop ((drift_scale g L).mono fun x h=> h.2.1) broad
lemma need (h:Host G (seats J j i s) X.L p s (ceilα J j i))(he:X.J=j)(Q:KernelChoices): ∀ᶠ x:ℝ in atTop, Request J α B j i Q X s p x:=by
   obtain ⟨T⟩:= pre_order G B.width B.paths j Q (n:=p+3) (by omega)
   let d:=grain B.clip X T (J.α j); have hd:= roundT p g J j B X T he -- args
   let Z:= Alto.tango J j i s p X α T d (T.tables B.clip X)
   have hV:= bureau G Z p s (ceilα J j i) X.L (largeJ _ _ _ _ _ X α T d (T.tables _ _) h)
   have hw:Tendsto cWidth atTop (𝓝 0):=tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp broad)
   let f:= countV G X.L; have hp:Tendsto f atTop atTop:=tendsto_atTop_add_const_right atTop _ tendsto_id
   filter_upwards [(billU g X.L).eventually hV, hw.eventually (ge_mem_nhds (zonepos ..)), (hw.comp hp).eventually (ge_mem_nhds (show 0<J.α j/2 from (by have he:=J.alpha_pos j;positivity))), drift_scale g X.L, hw.eventually (ge_mem_nhds hd)] with x hx h₁ h₂ hh hb
   constructor; refine ⟨T,hx (cWidth x) (?_) h₁ _ hh.1 ?_ hh.2.1,h₁,h₂,?_,?_⟩
   · unfold cWidth; positivity
   · linarith only [hh.1,hh.2.2]
   · unfold cWidth; rw [div_div]; have he:=zero_lt_one.trans_le hh.1; have hp:=he.trans_le hh.2.1; apply one_div_le_one_div_of_le (by positivity); apply (pow_le_pow_left₀ hp.le hh.2.2 2).trans; nlinarith only [mul_le_mul_of_nonneg_right (show (3:ℝ) ≤ X.L.val by exact_mod_cast X.coarse) (sq_nonneg (flurry x)),sq_nonneg (flurry x)]
   exact (div_le_self (by unfold cWidth; positivity) (Nat.one_le_cast.mpr X.L.property)).trans hb
end YM.MSbar.Alto
