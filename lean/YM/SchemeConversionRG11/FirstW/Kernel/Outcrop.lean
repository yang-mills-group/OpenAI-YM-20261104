import YM.SchemeConversionRG11.FirstW.Kernel.Paid
/-! DCT also for integrable torus tails. uniform summable tails/cross-image bills. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Pert Pert.Align Lattice Topology
open scoped BigOperators Interval
variable {E : Type*} [NormedAddCommGroup E] {T : Itinerary}
variable {f : Board T E} {n : Side} {C : ℝ}
def billC (c : ℝ) := fun x:E4=> c/(1+‖x‖)^6
lemma billC_pay (c : ℝ) : Integrable (billC c) := by
  have h : Integrable (fun x:E4=> (1+‖x‖)^(-(6:ℕ):ℝ)) := integrable_one_add_norm (by norm_num [E4])
  have he : ∀ x : E4, (1+‖x‖)^(-(6:ℕ):ℝ)=((1+‖x‖)^6)⁻¹ := fun x=> by rw [Real.rpow_neg (by positivity),Real.rpow_natCast]
  unfold billC; simpa only [he,div_eq_mul_inv] using h.const_mul c
lemma outcrop (c : Side) (f : Site n→E) (hC : 0 ≤ C) (he : ∀ x, (1+growsOut (rpace c) x)^6* ‖f x‖ ≤ C) : ∀ v:E4, ‖chunk c f v‖ ≤ billC ((6:ℝ)^6*C) v := by
  intro v; rw [chunk_coord]; split
  next h=>
    let x : Site n := (wrap n) (Next.Rank.Radian.mark c v)
    have hv : ‖v‖ ≤ 6*growsOut (rpace c) x := chunk_side c v _ rfl h
    change ‖f x‖ ≤ _; unfold billC; rw [le_div_iff₀ (by positivity)]
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show 1+‖v‖≤6*(1+growsOut (rpace c) x) by linarith) 6) (norm_nonneg _)) (by rw [mul_pow]; linarith only [he x])
  next=> rw [norm_zero]; unfold billC; positivity
variable {c : ℕ→Side} {K : E4 → E} [NormedSpace ℝ E] [CompleteSpace E]
lemma far_local (hc : MarkGrid T c) (hp : 0≤C) (he : ∀ᶠ i in atTop, ∀ x, (1+growsOut (T.gap i) x)^6*‖f i x‖ ≤ C) (hK : ∀ᵐ v ∂volume, ∀ p : ∀ i, Site (T.period i), sails T p v → Tendsto (fun i=> f i (p i)) atTop (𝓝 (K v))) :
    Integrable K ∧ Tendsto (fun i=>(T.gap i)^4 • ∑ x : Site (T.period i), f i x) atTop (𝓝 (∫ x,K x)) := by
  let G (i : ℕ) := chunk (c i) (f i)
  have ev := he.mono (fun i hi=> (ae_of_all (volume : Measure E4) (outcrop (c i) (f i) hp (fun x=>hc i ▸ (hi x)))))
  have hm i : AEStronglyMeasurable (G i) volume := (chunk_birth ..).aestronglyMeasurable
  have hv := billC_pay ((6:ℝ)^6*C)
  have H:=hK.mono fun _ h=> chunk_land (F:=f) hc h
  have e := tendsto_integral_filter_of_dominated_convergence (F:=G) _ (Eventually.of_forall hm) ev hv H
  exact ⟨freeborn G hv hm ev H,e.congr (fun i=>by rw [hc]; exact chunk_value ..)⟩
lemma grow_pos (h : ℝ) (x : Site n) (hh : h>0) : 0 < growsOut h x := mul_pos hh (zero_lt_one.trans_le (unit_cy x))
def billCap : ℝ := (1:ℝ)+|∫ x, billC ((6:ℝ)^6*(2:ℝ)^6) x|
lemma cap_pos : 0 < billCap := by unfold billCap;positivity
def lag (x : Site n) := ((cy x)^3)⁻¹
lemma lag_light (x : Site n) : lag x ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (unit_cy x))
lemma lag_pos (x : Site n) : 0<lag x := inv_pos.mpr (pow_pos (zero_lt_one.trans_le (unit_cy x)) _)
lemma night_budget (n : Side) : ∑ x : Site n,(lag x)^2 ≤ billCap := by
  let f : Site n → ℝ:= fun x=> (lag x)^2
  have eq (x : Site n): f x=((cy x)^6)⁻¹ := by unfold f lag;rw [inv_pow,← pow_mul]
  have hv (x : Site n) : (1+growsOut (rpace 1) x)^6*‖f x‖≤(2:ℝ)^6 := by
    simp only [eq, growsOut,rpace]; have hi := unit_cy x
    have hp : 0 < cy x := zero_lt_one.trans_le hi
    rw [Real.norm_of_nonneg (by positivity)]
    calc _ ≤ (2*cy x)^6*((cy x)^6)⁻¹ := by gcongr;(norm_num; linarith)
         _ = _ := by rw [mul_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ hp.ne'),mul_one]
  have he : (∫ x, chunk 1 f x) ≤ ∫ x,billC ((6:ℝ)^6 * (2:ℝ)^6) x := by
    refine integral_mono (chunk_birth ..) (billC_pay ..) fun x=>?_ ; exact (le_abs_self _).trans (outcrop 1 f (by positivity : 0 ≤ (2:ℝ)^6) hv _)
  rw [chunk_value] at he
  norm_num [rpace] at he
  apply le_trans he
  exact le_trans (b:=|∫x,billC _ x|) (le_abs_self _) (by unfold billCap; norm_num)
lemma night_shift (x : Site n) : ∑ p : Site n,(lag (p-x))^2 ≤ billCap := by
  have h := night_budget n
  have eq := Equiv.sum_comp (Equiv.addRight (-x)) (fun p:Site n=> (lag p)^2)
  simp_rw [sub_eq_add_neg]
  exact eq.trans_le h
lemma night_cross (x y : Site n) : ∑ p : Site n, lag (p-x)*lag (p-y) ≤ 2*billCap := by
  have hv (p : Site n) : lag (p-x)*lag (p-y) ≤ lag (p-x)^2+lag (p-y)^2 := by nlinarith [sq_nonneg (lag (p-x)-lag (p-y))]
  apply le_trans (Finset.sum_le_sum (fun i (_:i∈Finset.univ)=>hv i))
  rw [Finset.sum_add_distrib]; linarith only [night_shift x, night_shift y]
-- mixed image strands with (3,3,3) weights scale as a shifted sum gaining period^(-1) at least
lemma night_tri (x y z : Site n) : cy (x-y)* ∑ p : Site n, lag (p-x)*lag (p-y)*lag (p-z) ≤ 4*billCap := by
  rw [Finset.mul_sum]; refine (Finset.sum_le_sum (g:=fun p:Site n=> lag (p-y)*lag (p-z) +lag (p-x)*lag (p-z)) (fun p hp=>?_)).trans (by rw [Finset.sum_add_distrib]; linarith only [night_cross y z, night_cross x z])
  have he : cy (x-y) ≤ cy (p-x)+cy (p-y) := by nth_rw 1 [← sub_add_sub_cancel x p y,show x-p=-(p-x) by abel]; exact (sum_cy ..).trans (by rw [cy_neg])
  have h (x : Site n) : cy x *lag x ≤ 1 := by
    have hv := unit_cy x; unfold lag; rw [← div_eq_mul_inv, div_le_one (pow_pos (zero_lt_one.trans_le hv) 3)]; exact le_self_pow₀ hv (by decide)
  have a := lag_pos (p-x); have b := lag_pos (p-y); have c := lag_pos (p-z)
  apply le_trans (mul_le_mul_of_nonneg_right he (by positivity)); rw [add_mul]
  refine add_le_add ?_ ?_
  · linarith only [mul_le_mul_of_nonneg_right (h (p-x)) (show 0≤lag (p-y)*lag (p-z) by positivity)]
  linarith only [mul_le_mul_of_nonneg_right (h (p-y)) (show 0≤lag (p-x)*lag (p-z) by positivity)]
end YM.RG11.FirstW
