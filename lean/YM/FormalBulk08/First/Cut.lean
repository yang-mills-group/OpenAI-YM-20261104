import YM.FormalBulk08.First.Rail
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.First
open Function Filter Set MeasureTheory Lattice RG Exterior Wilson Precision
open Stationary hiding shine Rays
open scoped Topology BigOperators ENNReal Matrix ContDiff Classical
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine Dove North Aster
open Next.Foundations PhysicalNext.Repeat.Legato
open Borough RG.Supply Push.PriceCompiler Dove.Lab
variable {G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{A:Levels G}{C:Family G}{W:Borough.Window G K}
lemma lambda_large (A:Levels G)(m): 1≤Lambda A m:= by have ht:=A.fits.delayed m; have hc:=Real.log_pos ht; unfold Lambda; linarith
lemma needed (A:Levels G)(i:ℕ)(v:ℝ) : ∃ m:ℕ,v ≤ sowing A.S i (i+m) := by
   have hv : Tendsto (fun m:ℕ=> A.S.scale (i+m)-A.S.scale i) atTop atTop:= by
       have he:=A.S.divergent.comp (Filter.tendsto_atTop_mono (f:=id) (g:=fun m=>i+m) (fun m:ℕ=>Nat.le_add_left ..) tendsto_id); exact tendsto_atTop_add_const_right _ (-A.S.scale i) he
   exact (hv.eventually_ge_atTop v).exists

def endV (A:Levels G)(m:ℕ)(v:ℝ):ℕ:=Nat.find (needed A m v)
lemma endV_peak (m v) (hp:0<v):
    0<endV A m v ∧ v ≤ sowing A.S m (m+endV A m v) ∧ sowing A.S m (m+endV A m v-1) < v := by
    let p:=endV A m v; have he:v≤ _ := Nat.find_spec (needed A m v); change v ≤ sowing A.S m (m+p) at he
    have hx:p>0:= by
       by_contra! h
       have h':p=0:=by omega
       rw [h',Nat.add_zero,sowing,sub_self] at he; exact hp.not_ge he
    refine ⟨hx,he,?_⟩; change sowing _ _ (m+p-1) < v; rw [show m+p-1=m+(p-1) by omega]; exact lt_of_not_ge (Nat.find_min (needed A m v) (show p-1<p by omega))
variable {Q:Spigot.Herald}{F:∀ j,Labels.Frame G j}{Y: Source.Hol G}
lemma receipt (hs:G.Simple)(p:Evergreens K Q F Y ρ W A)(m v)(hv:0<v):
    let j:=m+endV A m v -1
    let z:= ageZ (A.clock.hatBeta m)
    sowing A.S m (j+1) ≤ v + Real.log (z+G.slopeConstant*v) := by
   intro j z; obtain ⟨b,hV,h⟩:=endV_peak (A:=A) m v hv; obtain ⟨B,hB,P,Hp⟩:=p.payment j; have hj:m≤j:=by unfold j;omega
   have H : Real.log ((A.S.block j).val:ℝ) ≤ Real.log (z+G.slopeConstant*v):= Real.log_le_log (by positivity) (Hp.1.trans (P.trans ((ages G A hs p.beta hj).2.2.trans (add_le_add_right (mul_le_mul_of_nonneg_left h.le (Gauge.slopeConstant_pos hs).le) _))))
   refine le_trans (le_of_eq (show sowing A.S m (j+1)=sowing A.S m j + Real.log ((A.S.block j).val:ℝ) by rw [sowing,sowing,Schedule.scale_succ];ring)) (add_le_add h.le H)
lemma hat_slopes (A:Levels G)(hs:G.Simple): Tendsto (fun m=>A.clock.hatBeta m) atTop atTop:= tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos hs))
lemma lambda_slope (A:Levels G)(hs:G.Simple):Tendsto (Lambda A) atTop atTop:= tendsto_atTop_add_const_left _ _ (Real.tendsto_log_atTop.comp (hat_slopes A hs))
lemma top_gear (hs:G.Simple)(p:Evergreens K Q F Y ρ W A)(q:ℝ)(hq:1<q):
    let v i:=(Lambda A i)^q
    let N i:=i+endV A i (v i)
    (∀ i,N i≥ i+1 ∧ v i ≤ sowing A.S i (N i)) ∧ Tendsto (fun i=>sowing A.S i (N i) / v i) atTop (𝓝 1) := by
    intro v N
    have hx i: 1≤v i:= Real.one_le_rpow (lambda_large A i) (le_trans zero_le_one hq.le); have hu i:Lambda A i≤ v i := (show Lambda A i = (Lambda A i)^(1:ℝ) from (Real.rpow_one _).symm).trans_le (Real.rpow_le_rpow_of_exponent_le (lambda_large A i) hq.le)
    have hy i:0<v i:= zero_lt_one.trans_le (hx _); have h i:=endV_peak (A:=A) i _ (hy i); refine ⟨fun i=> ⟨Nat.add_le_add_left (h i).1 i,(h i).2.1⟩,?_⟩
    let B:=G.slopeConstant+4; have hb:0<B:= add_pos (Gauge.slopeConstant_pos hs) (by norm_num)
    have he:Tendsto v atTop atTop:= (tendsto_rpow_atTop (show 0<q from zero_lt_one.trans hq)).comp (lambda_slope A hs)
    have ht:Tendsto (fun i=>1+Real.log (B*v i) /v i ) atTop (𝓝 1):= by
       simp_rw [Real.log_mul hb.ne' (hy _).ne',add_div]; convert (tendsto_const_nhds (x:=(1:ℝ))).add (((tendsto_const_nhds (x:=Real.log B)).div_atTop he).add ((show Tendsto (fun i=> Real.log i /i) atTop (𝓝 0) from (by simpa using! (isLittleO_log_rpow_atTop zero_lt_one).tendsto_div_nhds_zero)).comp he)) using 1 <;> norm_num
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht (Eventually.of_forall fun i=>(one_le_div (hy i)).2 (h i).2.1) (Eventually.of_forall fun i=>?_)
    change sowing _ _ _ /v i ≤ _; have Hp:= receipt hs p i _ (hy i); have H : N i=N i -1 + 1:= by have h : 0< N i:= show 0 < i+endV A i (v i) from Nat.add_pos_right _ (h i).1; omega
    nth_rw 1 [H]; rw [div_le_iff₀ (hy _),add_mul,one_mul, div_mul_cancel₀ _ (hy _).ne']; refine le_trans Hp (add_le_add_right (Real.log_le_log (by exact add_pos (zero_lt_one.trans_le (progZ (p.beta i))) (mul_pos (Gauge.slopeConstant_pos hs) (hy i))) (?_)) _)
    have he:= (spend p i).2; unfold B; nlinarith only [he, hx i,hu i]
end YM.FormalBulk08.First
