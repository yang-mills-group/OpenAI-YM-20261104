import YM.XSpace.Brine
/-!
# The line distributions of the leading angular calculation
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Season
open Function Filter Set MeasureTheory Relief Trace Litter Tide Sail Octave Playpen Lattice Further.FreeCovariance.KP
open Maxwell (Green grad)
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{A:Toe}{f:Breeze}
local notation "D₀" => Maxwell.Green
variable (t:Axis)(φ:Breeze) (h:ContDiff ℝ 1 φ)(H:HasCompactSupport φ) (s:Stage L a)
include s t h H in
lemma costs3 [L.IsCountablyGenerated][NeBot L](p:Beam 3 A f): Consummate L (fun i w=> a i*(A w*glass φ (a i) w)) (fun w=> f w*φ w):=by
  obtain ⟨C,hC,X⟩:= sonar (show A∈Terrain 3 from p.glows); obtain ⟨D,hD,Y⟩:= boundsT t φ H; obtain ⟨E,hE⟩:= h.continuous.bounded_above_of_compact_support H; have he:0≤E:= (norm_nonneg _).trans (hE 0); apply price s (C*E) D (mul_nonneg hC.le he); swap
  · filter_upwards [almost_all] with w hw; unfold down; refine ((shines s (marks w s.zero s.good) hw p).mul (show Tendsto (fun i=> glass φ (a i) (mark (a i) w)) L (𝓝 (φ w)) from h.continuous.continuousAt.tendsto.comp (marks w s.zero s.good))).congr' (s.good.mono fun i hi=>?_ ); field_simp
  filter_upwards [s.good,s.zero.eventually (ge_mem_nhds zero_lt_one)] with i hi hh x hx; refine ⟨Y _ hi hh x (Or.inl (right_ne_zero_of_mul (right_ne_zero_of_mul hx))),?_⟩; rw [norm_mul,norm_mul,Real.norm_of_nonneg hi.le]; exact (mul_le_mul_of_nonneg_left (mul_le_mul (X _) (hE _) (norm_nonneg _) (mul_nonneg hC.le (sound ..).le)) hi.le).trans_eq (by ring)
include s h H in
lemma mild2 [L.IsCountablyGenerated][NeBot L](p:Beam 2 A f): Consummate L (fun i w=> a i*(A w*η t (glass φ (a i)) w)) (fun w=> f w*(- grad t φ w)):=by
  obtain ⟨C,hC,X⟩:= sonar (show A∈Terrain 2 from p.glows); obtain ⟨D,hD,Y⟩:= boundsT t φ H; obtain ⟨E,hE,K⟩:= payable t φ h H; apply price s (C*E*D) D (by positivity); swap
  · filter_upwards [almost_all] with w hw; unfold down; refine ((shines s (marks w s.zero s.good) hw p).mul (mercy t _ h s (marks w s.zero s.good))).congr' (s.good.mono fun i hi=>?_ ); field_simp
  filter_upwards [s.good,s.zero.eventually (ge_mem_nhds zero_lt_one)] with i hi hh x hx; have ht: a i*pad x ≤D:= Y _ hi hh x (by by_contra! he; apply right_ne_zero_of_mul (right_ne_zero_of_mul hx); change glass _ _ _-glass _ _ _=0; rw [he.1,he.2]; simp)
  refine ⟨ht,?_⟩; rw [norm_mul,norm_mul,Real.norm_of_nonneg hi.le]; apply (mul_le_mul_of_nonneg_left (mul_le_mul (X _) (K _ hi x) (norm_nonneg _) (mul_nonneg hC.le (sound ..).le)) hi.le).trans; rw [← moon_paid 2 x]; calc
    _ = C*E*(a i*pad x)*a i*rate 3 x:=by ring
    _ ≤ _:=by have hp:0<rate 3 x:=sound ..; gcongr
abbrev dawn:=𝓝[>] (0:ℝ)
lemma starts : Stage dawn id:=⟨tendsto_nhdsWithin_of_tendsto_nhds tendsto_id, self_mem_nhdsWithin⟩
include h H in
lemma known_green : Integrable (fun w:E4=> grad t D₀ w*φ w) ∧ Integrable (fun w:E4=> D₀ w *grad t φ w)∧ (∫ x:E4,grad t D₀ x*φ x) = -(∫ x:E4, D₀ x * grad t φ x):=by
  have he:= costs3 t φ h H starts (greenBeam.step_forth t); have hh:= mild2 t φ h H starts greenBeam; refine ⟨he.2,?_ ,?_⟩; · simpa using hh.2.neg
  rw [← integral_neg]; simp_rw [← mul_neg]; refine tendsto_nhds_unique (he.1.congr' ?_) hh.1; filter_upwards [starts.good] with i hi; rw [tsum_mul_left,tsum_mul_left]; apply congr_arg; exact duet_dual Sail.cover (glass φ _) t (glass_sum φ H (fun w=> cover (w+step t)) (id i) hi) (glass_sum φ H _ _ hi)
end YM.XSpace.Season
