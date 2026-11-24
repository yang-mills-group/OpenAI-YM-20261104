import YM.MSbar.Mosaic.Index
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
variable {G:Gauge}(s:Side){ι τ:Type*}{X f g:ι→ℝ}{φ: Filter ι}{L:ℝ}
noncomputable def lensT (x t:ℝ):Prop:= cue x/2 ≤ t ∧ t ≤2* cue x
lemma ever {x t:ℝ}(h:0<x)(hr:x/2 ≤ t)(hp:t ≤2*x) : lensT x (cue t):=by
     have ht:0<t:= lt_of_lt_of_le (half_pos h) hr
     let y:= Real.sqrt x; let z:= Real.sqrt t; have hy:0< y:= Real.sqrt_pos.mpr h; have hz:0<z:= Real.sqrt_pos.mpr ht; have hf:y^2=x:=Real.sq_sqrt h.le; have hq:z^2=t:=Real.sq_sqrt ht.le
     have hE : y ≤ 2*z ∧ z ≤ 2*y:=by constructor<;> nlinarith
     constructor<;> unfold cue<;> change _≤ _
     · apply le_trans _ (inv_anti₀ hz hE.2); unfold y; ring_nf; field_simp; apply le_refl
     have hk:y/2 ≤ z:=by linarith only [hE]
     exact (inv_anti₀ (half_pos hy) hk).trans_eq (by unfold y; field_simp)
local notation "f!" i=> f i
variable (hX:Tendsto X φ atTop)
variable (he:∀ᶠ i in φ,lensT (X i) (f i))
include hX
lemma sands (t:ℝ→ℝ)(h:Tendsto t atTop atTop)(V:ℝ):∀ᶠ x in φ,V ≤ t (X x):=(h.comp hX).eventually_ge_atTop V
include he
lemma cuff:∀ᶠ i in φ,0< f i:=by
     filter_upwards [he,hX.eventually_gt_atTop 0] with i he hi; exact (half_pos (inv_pos.mpr (Real.sqrt_pos.mpr hi))).trans_le he.1
lemma charges:Run φ X f (-(1/2))∧Run φ X (fun x=> (f x)⁻¹) (1/2):=by
     obtain ⟨ht,hv⟩:= Run.waxing hX; refine ⟨(ht.mulK hX 2).cash ?_,(hv.mulK hX 2).cash ?_⟩
     · filter_upwards [he,cuff hX he] with i he hx; simpa only [abs_of_nonneg hx.le] using le_trans he.2 (le_abs_self _)
     filter_upwards [he,hX.eventually_gt_atTop 0,cuff hX he] with i he hi hh; let g:=cue (X i); have hg:0<g:=by unfold g cue; positivity
     apply le_trans _ (le_abs_self _); rw [abs_of_nonneg (inv_nonneg.mpr hh.le)]; exact (inv_anti₀ (half_pos hg) he.1).trans_eq (by rw [inv_div]; ring)
local notation "W" i =>room (X i)
omit he
lemma height (p :Palisade) (Pp : Voice G): Run φ X (Stock.skies ∘ X) (-(1/2))∧ Run φ X (room∘ X) (-(1/2))∧ Run φ X (pillow∘ X) (-(1/2))∧ Run φ X (rot p ∘ X) (-(1/2))∧ Run φ X (topP Pp p ∘ X) (-1):=by
     have hz:=Real.tendsto_log_atTop.comp hX; have hr: Run φ X (distance ∘ X) (-(1/2)):= Run.Yrat hX (Run.core hX _) (Run.logP hX); have hE: Run φ X (Stock.skies∘ X) (-(1/2)):= Run.Yrat hX hr (Run.logP hX); have hp:Run φ X (pillow ∘ X) (-(1/2)):= hr.mulK hX 3
     have hT:Run φ X (Real.sqrt ∘ Real.log ∘ X) 0:= by
          refine (Run.logP hX).cash ?_; filter_upwards [hz.eventually_ge_atTop 1] with x hx; let s:= Real.log (X x); have hi:1 ≤ s:=hx; simp only [Function.comp_apply]; change |Real.sqrt s| ≤ |s|; have hh:=Real.sqrt_nonneg s; rw [abs_of_nonneg hh, abs_of_nonneg (by linarith only [hi])]; nlinarith only [Real.sq_sqrt (zero_le_one.trans hi),mul_nonneg (sub_nonneg.mpr hi) (zero_le_one.trans hi),hi,hh]
     have hk : Run φ X (rot p ∘ X) (-(1/2)):=Run.mulK hX hE _
     refine ⟨hE,Run.Yrat hX hr hT,hp,hk, ?_⟩
     unfold topP maxZ; let Qx:ℝ→ℝ:=fun _=>0
     refine Run.mulK hX (Run.loosen (Run.raise hX ((hk.mulK hX (shade G)).mulK hX 4) 2) ?_) _ -- syntax
     norm_num
include he
lemma minimal: Tendsto (fun i=>room (X i)/(f i*hatW (X i))) φ (𝓝 0):=by
     let Z(i):= Real.log (X i); have hZ:Tendsto Z φ atTop:= Real.tendsto_log_atTop.comp hX; let Y(i):=2*(Real.sqrt (Z i))⁻¹; have hY:Tendsto Y φ (𝓝 0):=by
          have he : Tendsto (fun i=>Real.sqrt (Z i)) φ atTop:= by simp_rw [Real.sqrt_eq_rpow]; exact (tendsto_rpow_atTop (by norm_num : 0 < (1:ℝ)/2)).comp hZ
          simpa only [Y,mul_zero] using! ((tendsto_inv_atTop_zero.comp he).const_mul (2:ℝ)); -- unfold Y
     refine squeeze_zero' ?_ ?_ hY
     · filter_upwards [cuff hX he,hZ.eventually_gt_atTop 0,hX.eventually_gt_atTop 0] with i hh he hg; apply div_nonneg _ _; · exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hg.le _) he.le) (Real.sqrt_nonneg _)
       exact mul_nonneg hh.le (sq_nonneg _)
     filter_upwards [he,cuff hX he,hX.eventually_gt_atTop 0,hZ.eventually_gt_atTop 0] with i hx hi he hh; have hc:0<hatW (X i):= pow_pos hh _; have hm:0<Real.sqrt (Z i):=Real.sqrt_pos.mpr hh; have hU:0 ≤ Y i:=mul_nonneg zero_le_two (inv_nonneg.mpr hm.le); apply div_le_iff₀ (mul_pos hi hc)|>.mpr; apply le_trans _ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx.1 hc.le) hU); unfold room distance; rw [Real.rpow_neg he.le,← Real.sqrt_eq_rpow]; apply le_of_eq; change cue (X i)*Z i*Real.sqrt (Z i)=2*(Real.sqrt (Z i))⁻¹*((cue (X i)/2)*Z i^2); generalize ht:cue (X i)= t; have hsq: Z i= (Real.sqrt (Z i))^2:=(Real.sq_sqrt hh.le).symm; generalize ht0:Real.sqrt (Z i)=v at *; rw [hsq]; field_simp
end YM.MSbar.Mosaic
