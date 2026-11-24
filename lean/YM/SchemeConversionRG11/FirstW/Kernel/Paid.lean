import YM.SchemeConversionRG11.FirstW.Kernel.Screen
/-! Continuous-space DCT upgrade for single-puncture grid kernels, 
via normalized torus Riemann tiles (single LP-anchored lift).
Use after regional decomposition including single-line difference transposition. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.FirstW
open Function Filter MeasureTheory Set Metric Lattice Pert Align Topology Next.Rank.Radian
open scoped BigOperators
variable {T : Itinerary}
abbrev rpace (c : Side) : ℝ := (c.val:ℝ)⁻¹
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Board T E}
def chunk {n : Side} (c : Side) (f : Site n→E) := fun x:E4=> ∑ s, (tileP c (Lattice.lift s)).indicator (fun _=>f s) x
omit [NormedSpace ℝ E] in
lemma chunk_birth {n : Side} (c : Side) (f : Site n→E) : Integrable (chunk c f) := by
  refine integrable_finsetSum _ (fun i _=> (integrable_indicator_iff (tiles ..).1).mpr ?_)
  refine integrableOn_const ?_
  intro h
  have H : 0 < volume.real (tileP c (Lattice.lift i)) := (tiles ..).2 ▸ pow_pos (positive _) _
  rw [Measure.real,h] at H; simp at H
lemma chunk_value {n : Side} [CompleteSpace E] (c : Side) (f : Site n→E) : (∫ x, chunk c f x) = (rpace c)^4 • ∑ s,f s := by
  unfold chunk; rw [integral_finsetSum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; rw [integral_indicator (tiles ..).1, setIntegral_const, (tiles ..).2]
  intro i _; apply (integrable_indicator_iff (tiles ..).1).mpr; apply integrableOn_const; intro H; have h : 0 < volume.real (tileP c (Lattice.lift i)) := (tiles ..).2 ▸ pow_pos (positive _) _
  rw [Measure.real,H] at h; simp at h; simp
omit [NormedSpace ℝ E] in
lemma chunk_coord {n : Side} (c : Side) (f : Site n→E) (x : E4) :
    chunk c f x = if lift ((wrap n) (mark c x))=mark c x then f (wrap n (mark c x)) else 0 := by
  unfold chunk; split
  next h=>
    have e : x∈tileP c (lift (wrap n (mark c x))) := h.symm
    rw [Finset.sum_eq_single (wrap n (mark c x)),indicator_of_mem e]
    · intro j _ hj; exact indicator_of_notMem (fun (h' : x∈tileP c (lift j))=>hj (by rw [show mark c x=lift j from h', wrap_lift])) _
    simp
  next h=> exact Finset.sum_eq_zero (fun i _=>indicator_of_notMem (fun (h' : x∈tileP c (lift i)) => h (by rw [show mark c x=lift i from h',wrap_lift])) _)
def MarkGrid (T : Itinerary) (c : ℕ→Side) := ∀ i, T.gap i=rpace (c i)
variable {c : ℕ→Side} {R C : ℝ} {K : E4→E}
lemma sample_rock (c : Side) (x : E4) : ‖x-Full.incVec (rpace c) (mark c x)‖≤4*rpace c := by
  have he:= rock (c:=c) x
  rw [dist_comm,dist_eq_norm] at he; exact he
lemma chart_mark (hc : MarkGrid T c) (v : E4) : Tendsto (fun i=> Full.incVec (T.gap i) (mark (c i) v)) atTop (𝓝 v) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _=>dist_nonneg) (fun i=>show _ ≤ 4*T.gap i from ?_) (by simpa only [mul_zero] using T.cutoff.const_mul 4)
  rw [dist_comm,dist_eq_norm,hc]; exact sample_rock ..
omit [NormedSpace ℝ E] in
lemma chunk_land (hc : MarkGrid T c) {v : E4} (hv : ∀ p : ∀ i, Site (T.period i), sails T p v → Tendsto (fun i=> F i (p i)) atTop (𝓝 (K v))) : Tendsto (fun i=>chunk (c i) (F i) v) atTop (𝓝 (K v)) := by
  have h := chart_mark hc v; have e:=seals h
  apply (hv (fun i=>wrap (T.period i) (mark (c i) v)) (sails_wrap h)).congr'
  exact e.mono fun i he=> by dsimp only; rw [chunk_coord,if_pos he]
def growsOut {n : Side} (h : ℝ) (x : Site n) := h * cy x
variable {n : Side} {f : Site n → E}
lemma chunk_side (c : Side) (v : E4) (x : Site n) (_h : x = wrap n (mark c v)) (hx : lift x=mark c v) : ‖v‖ ≤ 6*growsOut (rpace c) x := by
  let y := Full.incVec (rpace c) (mark c v); have h₁ : ‖v-y‖ ≤ 4*rpace c := sample_rock c v
  have h₂ : ‖y‖ ≤ 2 * (rpace c * (cy x-1)) := by dsimp only [y]; nth_rw 1 [← hx]; exact high_at _ (positive _).le
  apply le_trans (show ‖v‖ ≤ ‖v-y‖ + ‖y‖ from by simpa only [sub_add_cancel] using norm_add_le (v-y) y)
  unfold growsOut; nlinarith [unit_cy x,positive c]
def hood (C : ℝ) (R : ℝ) : E4→ℝ := (ball 0 R).indicator (fun x:E4=>C/‖x‖^3)
lemma hood_int {R C : ℝ} (hC : 0≤C) : Integrable (hood C R) := (integrable_indicator_iff measurableSet_ball).2 (integrableOn_ball_of_norm_le_rpow (α:=3) (C:=C) (by simp) (by norm_num [E4]) (Eventually.of_forall fun x : E4=> by rw [Real.rpow_neg (norm_nonneg x),show (3:ℝ)=((3:ℕ):ℝ) from by norm_num,Real.rpow_natCast,Real.norm_of_nonneg (by positivity),div_eq_mul_inv]) ((show Measurable (fun x:E4=>C/‖x‖^3) from (measurable_const.div (measurable_id.norm.pow_const _))).aestronglyMeasurable))
omit [NormedSpace ℝ E] in
lemma chunk_hood (c : Side) (hq : 0≤C) (hu : ∀ x,f x≠0 → growsOut (rpace c) x ≤ R) (hf : ∀ x, (growsOut (rpace c) x)^3*‖f x‖ ≤ C) :
    ∀ᵐ v ∂volume, ‖chunk c f v‖ ≤ hood (216*C) (6*R+1) v := by
  refine (volume.ae_ne 0).mono (fun v hv=> ?_)
  have hg : 0 ≤ hood (216*C) (6*R+1) v := indicator_nonneg (fun x _=>by positivity) _
  rw [chunk_coord]; split
  next h=>
    let x := wrap n (mark c v); change ‖f x‖ ≤ _; by_cases he : f x=0
    · rwa [he,norm_zero]; -- doesn't solve?
    have he1 := hu x he; have he2 : ‖v‖ ≤ 6*growsOut (rpace c) x := chunk_side _ _ _ rfl h
    rw [hood,indicator_of_mem (show v∈ ball (0:E4) (6*R+1) from mem_ball_iff_norm.mpr (by rw [sub_zero]; linarith only [he1,he2])),le_div_iff₀ (pow_pos (norm_pos_iff.mpr hv) 3)]
    exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) he2 3) (norm_nonneg _)) (by have he:=hf x; rw [mul_pow]; linarith only [he])
  next=> simpa only [norm_zero] using hg
omit [NormedSpace ℝ E] in
lemma freeborn {μ : Measure E4} (Y : ℕ→ E4→E) {p : E4→ℝ} (hp : Integrable p μ) (hi : ∀ j, AEStronglyMeasurable (Y j) μ) (h : ∀ᶠ j in atTop,∀ᵐ x ∂μ,‖Y j x‖≤p x) (hK : ∀ᵐ x ∂μ,Tendsto (fun j=> Y j x) atTop (𝓝 (K x))) : Integrable K μ := by
  refine hp.mono' ?_ ?_
  · exact aestronglyMeasurable_of_tendsto_ae _ hi hK
  obtain ⟨k,hk⟩:=eventually_atTop.1 h; filter_upwards [hK, ae_all_iff.mpr (fun i:ℕ => hk (i+k) (Nat.le_add_left ..))] with x hx he
  have ht := hx.norm
  refine le_of_tendsto ht ((eventually_ge_atTop k).mono (fun i hi=> ?_)); obtain ⟨j,rfl⟩:=Nat.exists_eq_add_of_le hi; rw [Nat.add_comm k]; exact he j
variable [CompleteSpace E]
lemma sum_local (hc : MarkGrid T c) (hp : 0≤C) (he : ∀ᶠ i in atTop, ∀ x, (F i x ≠ 0 → growsOut (T.gap i) x ≤ R) ∧ (growsOut (T.gap i) x)^3*‖F i x‖ ≤ C) (hK : ∀ᵐ v ∂volume, ∀ p : ∀ i, Site (T.period i), sails T p v → Tendsto (fun i=> F i (p i)) atTop (𝓝 (K v))) :
    Integrable K ∧ Tendsto (fun i=>(T.gap i)^4 • ∑ x : Site (T.period i), F i x) atTop (𝓝 (∫ x,K x)) := by
  let G (i : ℕ) := chunk (c i) (F i)
  have ev := he.mono (fun i hi=> chunk_hood (f:=F i) (c i) hp (fun x=>hc i ▸ (hi x).1) (fun x=>hc i ▸ (hi x).2))
  have hv : Integrable (hood (216*C) (6*R+1)) := hood_int (by positivity)
  have hm i : AEStronglyMeasurable (G i) volume := (chunk_birth ..).aestronglyMeasurable
  have H:=hK.mono fun _ h=> chunk_land (F:=F) hc h
  have e := tendsto_integral_filter_of_dominated_convergence (F:=G) _ (Eventually.of_forall hm) ev hv H
  exact ⟨freeborn G hv hm ev H,e.congr (fun i=>by rw [hc]; exact chunk_value ..)⟩
end YM.RG11.FirstW
