import YM.FormalBulk08.Avenue.Mist
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
lemma mantle (x:Pitch) : ‖axes x‖=‖x‖:= by
    apply le_antisymm
    · refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i=>?_); simp only [axes,Complex.norm_real]; exact norm_le_pi_norm ..
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i=> ?_; rw [←Complex.norm_real (x i)]; exact norm_le_pi_norm (axes x) i
lemma base_pier (x:Pitch)(h:‖x‖<Real.pi): axes x ∈ baseCube:= ⟨by ext;simp [axes],fun i=> ((norm_le_pi_norm x i).trans h.le)⟩
lemma hat_ne (x:Pitch)(h:x≠0):axes x≠0:= norm_pos_iff.mp ((mantle x).symm ▸ norm_pos_iff.mpr h)
lemma mon_size (i:Site n): ‖mon i‖=‖tone n (Lattice.lift i)‖:= by rw [←tone_maps,mantle]
lemma mon_peak (i:Site n)(hp:i≠0): mon i≠0 := norm_pos_iff.mp ((mon_size i).symm ▸ ((pitch_high n).trans_le (hefty i hp)))

def buckle (k:ℝ)(v:Train j)(p:Momentum): Matrix (TypeFace 1) (TypeFace 1) ℂ:= if p=0 then 0 else fieldD 1 k v p
def carnel (k:ℝ)(v:Train j)(n:Side) := realOf (spectral (fun p:Site n=> buckle k v (mon p)))
def stall (k:ℝ)(v:Train j)(x:Cover)(a b:TypeFace 1)(p:Pitch) : ℝ := (mode (axes p) x * buckle k v (axes p) a b).re
def titular : ℝ:= ((2*Real.pi)^4)⁻¹
lemma titular_p : 0<titular:= by unfold titular; positivity
def reins (k:ℝ)(v:Train j)(x:Cover)(a b:TypeFace 1):= titular * (∫ p:Pitch in ball 0 Real.pi,stall k v x a b p)
lemma canon_rate (x y:Cover)(a b:TypeFace 1)(v:Train j)(k:ℝ): carnel k v n (wrap n x,a) (wrap n y,b)= titular *((hop n)^4 •∑ i:Site n, stall k v (x-y) a b (tone n (Lattice.lift i))) := by
    unfold carnel realOf; rw [Matrix.map_apply,spectral_apply,←map_sub]; simp_rw [cell_wrap,stall,tone_maps]; rw [show Further.FreeCovariance.KP.meter n=↑(titular*(hop n)^4) from ?_]; swap;· unfold Further.FreeCovariance.KP.meter titular hop; push_cast; have hv : (2:ℂ)*(Real.pi:ℂ)≠0:= mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'); field_simp
    simp only [Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,zero_mul, sub_zero,mul_assoc]
lemma cargo_sym (k:ℝ)(v:Train j)(hk:0<k): (carnel k v n)ᵀ=carnel k v n := by
    rw [carnel,← realOf_adj, spectral_adj]; congr! 2;
    ext t a b; unfold buckle;split;exact congr_fun (congr_fun (Matrix.conjTranspose_zero ..) _) _
    next h=> rw [Matrix.conjTranspose_apply]; simp_rw [fieldD,mask_value,scaleD_one]; by_cases he:a=b;subst b;rw [if_pos rfl]; let H:=Train.D_cost k hk v (axisEquiv.symm a) (real_frequency t); rw [← H.of_real]; simp
             rw [if_neg he,if_neg (Ne.symm he),star_zero]
lemma stall_prices (hk:0<k)(hj:4 ≤ j) :∃ C:ℝ,0<C ∧ ∀ (v:Train j) (a b) (n:Side) (x:Cover)(i:Site n),i≠0→ ‖stall k v x a b (tone n (Lattice.lift i))‖≤ C/‖tone n (Lattice.lift i)‖^2:= by
    obtain ⟨d,C,hD,H⟩:=Flat.levelD_caps j hj k hk; refine ⟨max 1 C,lt_max_of_lt_left one_pos,fun v a b n x i hi=>?_⟩
    have ht:= mon_peak i hi; rw [stall,tone_maps,←mon_size, Real.norm_eq_abs]; refine le_trans (Complex.abs_re_le_norm _) ?_;rw [norm_mul, mode_real _ _ (real_frequency _),one_mul,buckle,if_neg ht, fieldD, mask_value]; split; next he => rw [scaleD_one]; exact ((H v (mon i) _ (mon_mem n _) ht).2).trans (by gcongr;exact le_max_right ..)
    rw [norm_zero]; positivity
lemma vacancy (k:ℝ)(v:Train j)(a b x) : stall k v x a b 0=0:=by rw [stall,show axes (0:Pitch)=0 from axes_origin,buckle,if_pos rfl]; simp
lemma welcome (k:ℝ)(hj:4≤ j)(v:Train j)(a b x)(p:Pitch)(hp:p ≠ 0)(ht:‖p‖<Real.pi): ContinuousAt (stall k v x a b) p:= by
   let A:= axes p; have ha: A∈ baseCube:=base_pier p ht; have he:Continuous (axes:Pitch→Momentum):= (axisCL Axis).continuous
   have hv : ∀ᶠ p : Pitch in 𝓝 p, p≠0 ∧ ‖p‖ < Real.pi := (eventually_ne_nhds hp).and (continuous_norm.continuousAt (gt_mem_nhds ht))
   have hl : ContinuousAt (fun p:Pitch=>buckle k v (axes p) a b) p:= by

      by_cases hy:a=b; swap
      · apply (continuousAt_const (y:= (0:ℂ))).congr; filter_upwards [hv] with p hp; rw [buckle,if_neg (hat_ne p hp.1),fieldD];rw [mask_value,if_neg hy]
      let i:= axisEquiv.symm a
      have ho : ContinuousAt (fun p:Momentum=> v.bulb k p i / divisor v.mass p) A:= by
         obtain ⟨W,B,hW,hB,H⟩:=Train.bulb_budget k hj (fun _:Unit=>v) (fun _=>i); apply ContinuousAt.div; exact ((H ()).hol A (mem_cube_real (base_subset_realCube hW ha) hW)).continuousAt
         obtain ⟨W,B,hW,hB,H⟩:=divisor_control (fun _:Unit=>v.mass); exact ((H ()).hol A (mem_cube_real (base_subset_realCube hW ha) hW)).continuousAt
         exact divisor_ne _ (base_subset_realCube zone_pos ha) (hat_ne p hp)
      refine (ho.comp he.continuousAt).congr ?_; filter_upwards [hv] with p hp; rw [buckle,if_neg (hat_ne p hp.1),fieldD, mask_value,if_pos hy,scaleD_one]; exact Eq.symm (Train.D_bulb k v (base_subset_realCube zone_pos (base_pier p hp.2)) (hat_ne p hp.1) i)
   have hy : Continuous fun y:Pitch=>mode (axes y) x:= by unfold mode;fun_prop
   exact Complex.continuous_re.continuousAt.comp ((hy.continuousAt (x:=p)).mul hl)
end YM.FormalBulk08.Avenue
