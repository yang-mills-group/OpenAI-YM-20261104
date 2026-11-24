import YM.LocalLTE.Units.Vain
/-! C^inf from stage N. varying coefficient prices via real-uniform pointwise. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Cabana
open Function Filter Set Metric ContinuousMultilinearMap Tensor PhysicalNext.Repeat ConnectedActivityE6.Blaze Brush
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g:ℕ→E→ℝ}{u v w c:ℝ} {K:E→ℝ}{n j : ℕ} {V: ℝ} {ι:Type*}{φ:Filter ι}
open Metric
omit [FiniteDimensional ℝ E] in
lemma hovering {X:Set E}{v:ι→ E→ℝ} {c:ℝ}(hp:IsCompact X)(h:Convex ℝ X)(hz:∀ x∈X,Tendsto (fun n=>v n x) φ (𝓝 0))(hh:∀ᶠ i in φ,∀ x∈X,Brush 1 c 1 (v i) x) (ε:ℝ) (he:0<ε) : ∀ᶠ i in φ, ∀ x∈X, ‖v i x‖ < ε:=by
   have hr:0 < 2*(|c|+1):=by positivity
   let r:= ε/(2*(|c|+1)); have hf:0<r:= div_pos he hr
   obtain ⟨I,hI,H⟩:= hp.elim_nhds_subcover (fun x=>Metric.ball x r) (fun x hx=>Metric.ball_mem_nhds _ hf)
   have ht: |c| *r ≤ ε/2:= by unfold r; rw [mul_div_assoc',div_le_iff₀ hr]; linarith -- edit
   filter_upwards [hh,(eventually_all_finset I).mpr fun x hx=> (((continuous_norm.continuousAt.tendsto.comp (hz x (hI _ hx))).eventually (gt_mem_nhds (show ‖(0:ℝ)‖< ε/2 by rw [norm_zero]; exact half_pos he))))] with i hV he' x hx
   obtain ⟨y,ht',hy'⟩:= Set.mem_iUnion₂.mp (H hx)
   have hp:= (mem_ball.mp hy'); rw [dist_eq_norm] at hp
   have hL : ‖v i x-v i y‖ ≤ |c| *‖x-y‖:= h.norm_image_sub_le_of_norm_fderiv_le (fun z hz=> (hV z hz).smooth.differentiableAt (by norm_num)) (fun x hx=> le_trans (by simpa only [normJ, norm_iteratedFDeriv_one,pow_one, mul_one] using (hV x hx).order 1 le_rfl) (le_abs_self _)) (hI _ ht') hx
   have he' : ‖v i y‖ < ε/2:= he' y ht'
   linarith only [(norm_le_insert' (v i x) (v i y)),hL,mul_le_mul_of_nonneg_left hp.le (abs_nonneg c),ht,he'] -- edit
omit [FiniteDimensional ℝ E] in
lemma dart_norm {r:ℝ}(h:0≤r)(x:E)(hx:Dart 0 r x): ‖x‖≤r:= by obtain ⟨z,hz,hx⟩:=hx; simp only [smul_zero,sub_zero] at hx; exact hx.trans (mul_le_of_le_one_left h hz.2) -- nonneg r need
lemma nimble {v:ι→ E→ℝ} (h:j < n) (hu:0<u)(hV:0≤V) (hp:∀ x,‖x‖<u → Tendsto (fun i=> v i x) φ (𝓝 0)) (he:∀ᶠ i in φ,∀ x:E,‖x‖<u→ Brush n V 1 (v i) x):
    Tendsto (fun i=>iteratedFDeriv ℝ j (v i) 0) φ (𝓝 0):=by
   obtain ⟨L,hL,H⟩:= resurrect n j h
   apply Metric.tendsto_nhds.mpr; intro ε hε
   let V':=1+V; let f:=(L*(1+V)); let W:=min (u/2) (min 1 (ε/((L*(1+V))+1)/2))
   have h':0<W:=lt_min (half_pos hu) (lt_min zero_lt_one (by positivity)); have hU:W<u:=lt_of_le_of_lt (min_le_left ..) (half_lt_self hu); have h₁:W ≤ 1:= (min_le_right ..).trans (min_le_left ..); have hz : f*W < ε:= by
      have he:W ≤ ε/(f+1)/2:= (min_le_right ..).trans (min_le_right ..)
      have hp:0<f+1:= by unfold f; positivity
      have hx:= (le_div_iff₀ hp).mp ((le_div_iff₀ zero_lt_two).mp he)
      nlinarith only [h',hx,mul_pos h' hp] -- edit
   let p:=Metric.closedBall (0:E) W; have hp₁ {x:E}(hx: x∈p): ‖x‖<u:=(mem_closedBall_zero_iff.mp hx).trans_lt hU
   have hw:= hovering (v:=v) (isCompact_closedBall 0 W) (convex_closedBall 0 W) (fun x h=>hp _ (hp₁ h)) (by filter_upwards [he] with i h; exact (show ∀ x, x∈p → Brush 1 V 1 (v i) x from fun x hx=> (h x (hp₁ hx)).smaller (show 1≤n by omega))) (W^n) (by positivity)
   filter_upwards [he,hw] with i hi hi'; rw [dist_zero_right]
   have hK:= H E (v i) 0 0 W W V (W^n) h' (by rw [norm_zero,zero_add]) hV (pow_pos h' n).le (fun y hy=>?_)|>.order j (le_refl _); swap
   · have he:y∈p:= mem_closedBall_zero_iff.mpr (dart_norm h'.le y hy)
     rw [add_zero]; have h:= hi _ (hp₁ he); refine ⟨h.smooth,?_, (hi' _ he).le⟩; simpa only [one_pow,mul_one] using! h.order n le_rfl
   apply hK.trans_lt; apply lt_of_le_of_lt _ hz; have hS: W^n ≤ W^(j+1):= pow_le_pow_of_le_one h'.le h₁ (by omega : j+1≤n)
   rw [show L * (W^n+V*W^n)=L*(1+V)*W^n by ring]; apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) (by positivity)); exact le_of_eq (by unfold f; rw [inv_pow,pow_succ]; field_simp) -- edit
lemma flight {f:ι→ E→ℝ} (hu:0<u)(hp:∀ x,‖x‖<u→ Tendsto (fun i=>f i x) φ (𝓝 (K x))) (hx:∀ᶠ i in φ,∀ x:E,‖x‖<u→ Brush n V 1 (f i) x)(hg:∀ x:E,‖x‖<u → Brush n V 1 K x) (h:j < n): Tendsto (fun i=> Tensor.coeff (f i) j 0) φ (𝓝 (Tensor.coeff K j 0)):=by
   have h':=hg 0 (by rwa [norm_zero]); let g(i:ι):= f i-K
   have ht:= Cabana.nimble (v:=g) h hu (add_nonneg h'.nonneg h'.nonneg) (fun x h=>by simpa only [g,sub_self] using! ((hp x h).sub (tendsto_const_nhds (x:=K x)))) (by filter_upwards [hx] with i hi; exact (show ∀ x:E,‖x‖<u→ Brush n (V+V) 1 (g i) x from fun x hx=> (hi _ hx).separating (hg _ hx)))
   have he:= (ht.add (tendsto_const_nhds (x:=iteratedFDeriv ℝ j K 0))).const_smul ((j.factorial:ℝ)⁻¹); rw [zero_add] at he; apply he.congr'; filter_upwards [hx] with i hi; dsimp only [g]; rw [iteratedFDeriv_sub_apply ((hi 0 (by rwa [norm_zero])).smooth.of_le (Nat.cast_le.mpr h.le)) (h'.smooth.of_le (Nat.cast_le.mpr h.le)),sub_add_cancel]; rfl
end YM.LocalLTE.Cabana
