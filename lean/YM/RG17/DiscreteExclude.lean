import YM.RG17.ViaTrace
import YM.RG17.Squaring

/-!
# Sparse Euclidean coefficient and Fock test

For a single chosen Euclidean sequence of lengths. All-phase only as
Trace2. No Fock estimates attempted on these families independent of
`Shell.Comparison` itself. Does not wait for full-scale log law.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.RG17
open Function Set Filter MeasureTheory Spec Extraction Table OPE OPE.Orbits
open Next.UVStress Boundary Trace Complex
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} {C:Family G}{f: Order} {S:Table C.book} (F:Final C f S)
open TracePay

-- isolate h exponent 9 to get using actual every continuous lengths upper, for this phase
lemma poisedPower (h : Services C f S) : Tendsto (fun r:ℝ=> (r⁻¹)^9* ‖restTrace F (meanExact F) r⁻¹‖) atTop (𝓝 0):= by
    have hi:= Trace.uniform_upper F h 9 (by norm_num) (fun _ : ℝ=> some F.α.atPoint)
    refine (hi.comp tendsto_inv_atTop_nhdsGT_zero).congr (fun x=>?_)
    rw [restTrace_origin]; change (x⁻¹)^(9:ℝ)*_= (x⁻¹)^(9:ℕ)*_
    congr 1
    exact_mod_cast Real.rpow_natCast x⁻¹ 9

def SampleLog (L: Filter ℝ) (κ:ℝ) := Tendsto (fun r:ℝ=> (discount r • restTrace F (meanExact F) r)) L (𝓝 (↑κ:ℂ)) -- length form
section numeric
variable {b:Filter ℝ} (hb:b ≤ atTop)
include hb
private lemma unSquare (m:ℕ)(y:ℝ→ℝ) (h:∀ᶠ r in b,0≤y r)(hy:Tendsto (fun r=> (r⁻¹)^(m*2)*y r^2) b (𝓝 0)) :
    Tendsto (fun r=> (r⁻¹)^m*y r) b (𝓝 0):=by
   have hp:= hy.sqrt; rw [Real.sqrt_zero] at hp
   refine hp.congr' ?_; filter_upwards [h,(eventually_gt_atTop (0:ℝ)).filter_mono hb] with r hr ht
   rw [pow_mul, ← mul_pow,Real.sqrt_sq (by positivity)]
private lemma extinguish (y:ℝ→ℝ) (h:∀ᶠ r in b,0≤y r) (H:∃ c:ℝ,∀ᶠ t in b,t⁻¹^6*y t ≤ c): Tendsto (fun t=> logWeight t*y t) b (𝓝 0):=by
   obtain ⟨c,hc⟩:=H
   have hh:=Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.mono_left hb
   refine squeeze_zero' ?_ (g:=fun t:ℝ=> (Real.log t/t)^2*c) ?_ (by simpa using (hh.pow 2).mul_const c)
   · filter_upwards [(eventually_gt_atTop (1:ℝ)).filter_mono hb,h] with i hi hk; exact mul_nonneg (positive_weight hi|>.le) hk
   filter_upwards [hc,(eventually_gt_atTop (0:ℝ)).filter_mono hb] with t ht hp
   refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left ht (sq_nonneg (Real.log t/t))); unfold logWeight; ring
end numeric
lemma sampleClose (h : Services C f S){b:Filter ℝ}[b.NeBot](hb:b ≤ home){κ:ℝ}(hp:κ>0) {m:ℕ} (U:F.action.operators.H →ₗᵢ[ℂ] Shell.Sum m)(he:SampleLog F b κ):¬ Shell.Comparison F (meanExact F) U := by
   let a:= map Inv.inv b
   haveI : a.NeBot := inferInstanceAs (Filter.map _ _).NeBot
   have ha : a ≤ atTop:=(tendsto_inv_nhdsGT_zero.mono_left hb)
   intro hw
   obtain ⟨M,hm,hM,hT,H⟩:= centered_spectral F
   let e (t:ℝ):=∫ p,Real.exp (-(t⁻¹)*time p)∂M
   have hh(t:ℝ)(ht:0<t): restTrace F (meanExact F) t⁻¹=↑(e t):=hT _ (inv_pos.mpr ht)
   have hn (r:ℝ)(hr:0<r):0 ≤ e r:=integral_nonneg (fun _=> Real.exp_nonneg _)
   have hHeat:Tendsto (fun r:ℝ=> logWeight r* e r) a (𝓝 κ):=by
      apply tendsto_map'_iff.mpr
      have he : Tendsto _ b (𝓝 _):= he
      refine ((Complex.continuous_re.continuousAt.tendsto).comp he).congr' ?_
      filter_upwards [positiveLength.filter_mono hb] with t ht
      dsimp only [Function.comp_apply]; rw [discount_eq, Complex.real_smul, Complex.mul_re, (by simpa only [inv_inv] using hh t⁻¹ (inv_pos.mpr ht) : restTrace F (meanExact F) t=_)]; simp
   have hg:Tendsto (fun t=> (t⁻¹)^9*e t) atTop (𝓝 0):= (poisedPower F h).congr' <| (eventually_gt_atTop (0:ℝ)).mono fun t ht=> by rw [hh t ht,Complex.norm_real,Real.norm_of_nonneg (hn t ht)]
   obtain ⟨f,hf,hl⟩:= lowBill
   let v:= Shell.fockWave F (meanExact F) U
   have hz : ∀ t, ‖thetaV F (meanExact F) t‖=‖v t‖:=fun t=> (U.norm_map _).symm
   -- any epsilon <2 enough for this first cost (kept 1 here)
   have hq:=hw.data
   let HT : FieldsNorm M (thetaV F (meanExact F)):= H
   obtain ⟨A,hA,hA'⟩:= inferGrowth hm hM (hg.eventually (ge_mem_nhds one_pos))
   obtain ⟨P,hP⟩:= powerTest HT hA' hA f
   let p(t:ℝ):= ‖thetaV F (meanExact F) (normalized f t)‖
   have hp':Tendsto (fun t=> t⁻¹^5*p t) atTop (𝓝 0):= by
      apply unSquare (b:=atTop) le_rfl 5 p (Eventually.of_forall fun _=>norm_nonneg _) (squeeze_zero'
        ((eventually_gt_atTop (0:ℝ)).mono fun _ hi=> mul_nonneg (pow_nonneg (inv_pos.mpr hi).le _) (sq_nonneg _)) (g:=fun t:ℝ=> t⁻¹*P) ?_
        (by simpa only [zero_mul] using (tendsto_inv_atTop_zero (𝕜:=ℝ)).mul_const P))
      filter_upwards [hP,eventually_gt_atTop (0:ℝ)] with i hi hk
      rw [show 5*2=9+1 from rfl,pow_succ',mul_assoc]; exact mul_le_mul_of_nonneg_left hi (inv_pos.mpr hk).le
   have hs : Tendsto (fun t=>t⁻¹^(4+1)*‖v (normalized f t)‖) atTop (𝓝 0):= hp'.congr (fun i=>congr_arg _ (hz _))
   obtain ⟨C,hC,hC'⟩:= allSquared _ le_rfl 4 f v hw.data hf hs
   obtain ⟨B,hB,hB'⟩:= lowerTest (n:=8) HT hl hm ⟨C,hC,by intro r hr; rw [hz]; exact hC' r hr⟩
   obtain ⟨W,hW,hW'⟩:= finalOn B hB hB'
   have hb8:Tendsto (fun r:ℝ=> r⁻¹^8 * e r) a (𝓝 0):=by
      have he' := Real.tendsto_log_atTop.mono_left ha
      refine (hHeat.div_atTop (he'.atTop_mul_atTop₀ he')).congr' ?_
      filter_upwards [he'.eventually_ne_atTop 0] with i hi
      change logWeight i*e i/(Real.log i*Real.log i)=_
      unfold logWeight; field_simp
   have hs' := sparseSch ha hW' hW hM hb8 (normTest f)
   have ht' : Tendsto (fun r:ℝ=> r⁻¹^8*p r^2) a (𝓝 0):=by
      refine (Complex.continuous_re.continuousAt.tendsto.comp hs').congr' ?_
      filter_upwards [(eventually_gt_atTop (1:ℝ)).filter_mono ha] with i hi
      dsimp only [Function.comp_apply]; rw [normsMeter HT _ hi]; rfl
   have hs4 : Tendsto (fun t=>t⁻¹^(3+1)*‖v (normalized f t)‖) a (𝓝 0):= (unSquare ha 4 p (Eventually.of_forall fun _=>norm_nonneg _) ht').congr fun i=> congr_arg _ (hz _)
   obtain ⟨C',hK,hK'⟩:= allSquared a ha 3 f v hw.data hf hs4
   obtain ⟨D,hD,hD'⟩:= lowerTest (n:=6) HT hl hm ⟨C',hK,by intro r hr; rw [hz]; exact hK' r hr⟩
   obtain ⟨V,hV,hV'⟩:= finalOn D hD hD'
   obtain ⟨N,hN,hN'⟩:= growthHeat hV' hV hM
   exact hp.ne' (tendsto_nhds_unique hHeat (extinguish ha e
      (((eventually_gt_atTop (0:ℝ)).mono hn).filter_mono ha) ⟨N, ((eventually_ge_atTop 1).mono hN').filter_mono ha⟩))
end YM.RG17
