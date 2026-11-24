import YM.Trace.Fock.Flatness
/-! Singleton kernel inclusion on flat test jets. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option autoImplicit false
namespace YM.Trace.Shell
open MeasureTheory YM Filter Set Function Complex Boundary
open scoped Topology ContDiff Pointwise InnerProductSpace BigOperators
variable (f : Probe Mom)
private lemma cut_radii : ∃ B>0, ∀ t > (0:ℝ), tsupport (adjusted (ruler Mom) t⁻¹) ⊆ Metric.closedBall 0 (B*t) := by
     let h := ruler_CC (V:=Mom)
     obtain ⟨c,hc⟩ := h.isBounded.subset_ball 0
     refine ⟨max c 1, zero_lt_one.trans_le (le_max_right _ _),fun t ht => closure_minimal (t:=Metric.closedBall 0 (max c 1 * t)) (fun x hx=> Metric.mem_closedBall.mpr ?_) Metric.isClosed_closedBall⟩
     rw [dist_zero_right]
     have hu := hc (subset_tsupport (f:=(ruler Mom)) (by change ruler Mom (t⁻¹ • x)≠0; intro h; apply hx; change adjusted (ruler Mom) t⁻¹ x = 0; rwa [adjusted_eq _ (inv_ne_zero ht.ne')]))
     apply (lt_of_lt_of_le ?_ (mul_le_mul_of_nonneg_right (le_max_left ..) ht.le)).le (a:=_) -- fix parser
     rw [← div_lt_iff₀ ht]
     refine (le_of_eq (b:=‖t⁻¹ • x‖) (by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),div_eq_inv_mul])).trans_lt (by rw [Metric.mem_ball,dist_zero_right] at hu; exact hu)

lemma cut_exact (t : ℝ) (h : t>0) : (⇑(cutTest f t)) =ᶠ[𝓝 0] ⇑f := Filter.Eventually.mono (p:=fun (i:Mom)=> i∈Metric.ball 0 t) (Metric.ball_mem_nhds 0 h) (fun i hi=> by
     have hh : ‖t⁻¹ • i‖ ≤ 1 := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),← div_eq_inv_mul,div_le_one h]; exact (by simpa using hi : ‖i‖ < t).le
     rw [cutTest_eq _ h.ne',ruler_one hh,mul_one])
lemma cut_flat {k : ℕ} {t:ℝ} (h : t>0) (he : FlatAns k 0 f) : FlatAns k 0 (cutTest f t) := fun j hj i=> by rw [monomialJet,show iteratedFDeriv ℝ j (cutTest f t:Mom→ℂ) 0=iteratedFDeriv ℝ j (f:Mom→ℂ) 0 from (cut_exact f t h|>.iteratedFDeriv ℝ j).eq_of_nhds]; exact he j hj i

private lemma near_bound (f :Probe Mom) {k : ℕ} (s) (hs : s ≤ k) (hf : FlatAns (2*k+1) 0 f) :
  ∃ C > (0:ℝ), ∀ j∈Finset.range (s+1), ∀ x:Mom, ‖x‖≤1 → jj j f x ≤ C*‖x‖^(k+1) := by
    suffices H : ∀ j, ∃ C > (0:ℝ), ∀ x:Mom, j ≤ s → ‖x‖≤1 → jj j f x ≤ C*‖x‖^(k+1) by
       choose c hc hc' using H
       exact ⟨max 1 (∑ i∈Finset.range (s+1), c i),zero_lt_one.trans_le (le_max_left ..),fun j hj x hx => (hc' j x (by simpa [Nat.lt_succ_iff] using hj) hx).trans (mul_le_mul_of_nonneg_right (le_trans (Finset.single_le_sum (f:=c) (fun t _=>(hc t).le) hj) (le_max_right ..)) (by positivity))⟩
    intro i; by_cases hi:i≤s
    · obtain ⟨c,hc,hM⟩ := jets_bound (2*k+1) f hf (k+1) i (by omega)
      exact ⟨max 1 c, zero_lt_one.trans_le (le_max_left ..),fun x _ hx=> (hM x hx).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))⟩
    exact ⟨1,by positivity,fun x h=> False.elim (hi h)⟩

private lemma small_at (f : Probe Mom) {a b k : ℕ} (hb : b ≤ k) (B : ℝ) (hB : B≥1)
    (C : ℝ) (hC : C>0) (hc' : ∀ j ∈ Finset.range (b+1), ∀ x:Mom, ‖x‖≤1→ jj j f x ≤ C*‖x‖^(k+1)) : let D j := (b.choose j : ℝ) * C * B^(k+1) * Probe.size 0 (b-j) (ruler Mom)
       ∀ t > 0, t≤1→B*t≤1 → tsupport (cutTest f t) ⊆ Metric.closedBall 0 (B*t) → ∀ x:Mom, (‖x‖^a) * jj b (cutTest f t) x ≤ (∑ j ∈ Finset.range (b+1), D j)*t := by
    intro D t ht ht' hB' hsup x
    have ps (n) : 0≤ Probe.size 0 n (ruler Mom) := apply_nonneg ..
    let C₁ := ∑ j ∈ Finset.range (b+1), D j
    have BD (i) : 0≤D i:=by dsimp only [D]; have:=ps (b-i); have:=show (0:ℝ)≤ B from zero_le_one.trans hB; positivity
    have BC : 0≤C₁:=Finset.sum_nonneg fun i _=> BD i
    let q := adjusted (ruler Mom) t⁻¹
    by_cases h : ‖x‖≤B*t
    · have hZ : ‖x‖^a ≤1 := pow_le_one₀ (norm_nonneg _) (h.trans hB')
      refine (mul_le_of_le_one_left (jj_nonneg b ..) hZ |>.trans (product_j_ineq f _ b x)).trans ?_
      rw [Finset.sum_mul]; apply Finset.sum_le_sum _
      intro i hi
      have hh : ‖x‖^(k+1) ≤ (B*t)^(k+1) := pow_le_pow_left₀ (norm_nonneg _) h _
      have hM : 0 < C*(B*t)^(k+1) := by have := zero_lt_one.trans_le hB; positivity
      have hk' : 1≤t⁻¹ := one_le_inv₀ ht|>.mpr ht'
      have htQ : jj (b-i) q x ≤ (t⁻¹)^k * Probe.size 0 (b-i) (ruler Mom) := ((jj_le ..).trans (adjusted_size _ hk' 0 (b-i))).trans (by gcongr; omega)
      have hF : jj i f x ≤ C*(B*t)^(k+1) := (hc' i hi x (h.trans hB')).trans (mul_le_mul_of_nonneg_left hh hC.le)
      calc _ ≤ ↑(b.choose i) * (C*(B*t)^(k+1)) * ((t⁻¹)^k * Probe.size 0 (b-i) (ruler Mom)) := mul_le_mul (mul_le_mul_of_nonneg_left hF (by positivity)) htQ (jj_nonneg ..) (by positivity)
           _ = _ := by dsimp only [D]; rw [mul_pow,inv_pow,pow_succ]; field_simp; ring
    have htZ := tsupport_iteratedFDeriv_subset (f:=(cutTest f t)) (𝕜:=ℝ) b |>.trans hsup
    have hn : iteratedFDeriv ℝ b (⇑(cutTest f t)) x=0 := image_eq_zero_of_notMem_tsupport (fun hm => h (by simpa using! htZ hm))
    simpa only [jj,hn,norm_zero,mul_zero] using mul_nonneg BC ht.le

private lemma small_supp (f : Probe Mom) (B) (hB' : ∀ t>(0:ℝ),tsupport (adjusted (ruler Mom) t⁻¹)⊆Metric.closedBall 0 (B*t)) (t : ℝ) (ht : t>0):
       tsupport (cutTest f t) ⊆ Metric.closedBall 0 (B*t) := by
        refine closure_minimal (s:=support ((cutTest f t) : Mom→ℂ)) (fun x (hx: cutTest f t x≠0)=> hB' _ ht (subset_tsupport (f:=adjusted (ruler Mom) t⁻¹) (fun he=>hx ?_))) Metric.isClosed_closedBall
        unfold cutTest; rw [Probe.sews,he,mul_zero]
lemma zero_size {k : ℕ} (hf : FlatAns (2*k+1) 0 f) (a b) (h : b≤k) :
    Tendsto (fun t=> Probe.size a b (cutTest f t)) (𝓝[>]0) (𝓝 0) := by
    obtain ⟨B,hB,hSup⟩ := cut_radii
    obtain ⟨C,hC,hc⟩ := near_bound f b h hf
    let M := ∑ j ∈ Finset.range (b+1), ((b.choose j : ℝ)*C*(max B 1)^(k+1)* Probe.size 0 (b-j) (ruler Mom))
    have hA := small_at (a:=a) (k:=k) f h (max B 1) (le_max_right ..) C hC hc
    suffices HE : (fun t => Probe.size a b (cutTest f t)) ≤ᶠ[𝓝[>]0] fun t => M * t by
       exact squeeze_zero' (.of_forall fun _=> apply_nonneg ..) HE (by simpa using! (((continuous_const_mul M).tendsto 0).mono_left nhdsWithin_le_nhds))
    filter_upwards [self_mem_nhdsWithin, show ∀ᶠt:ℝ in 𝓝[>]0,t ∈ Set.Ioo (-(1:ℝ)) (max B 1)⁻¹ from mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by exact inv_pos.mpr (zero_lt_one.trans_le (le_max_right ..))))] with t (ht : t>0) ⟨hL,ht₁⟩
    have hr : 0<max B 1 := zero_lt_one.trans_le (le_max_right ..)
    have hB₁ : max B 1*t≤1 := by exact ((lt_inv_mul_iff₀ hr).1 (ht₁.trans_eq (by rw [mul_one]))).le; -- check
    have ht₂ : t≤1 := ht₁.le.trans (inv_le_one_of_one_le₀ (le_max_right ..)) -- wrong trans
    have hsup : tsupport (cutTest f t) ⊆ Metric.closedBall 0 (max B 1*t) := small_supp f _ hSup t ht|>.trans (Metric.closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (le_max_left ..) ht.le))
    apply SchwartzMap.seminorm_le_bound ℂ a b _ _ _
    · unfold M; apply mul_nonneg (Finset.sum_nonneg (fun i _=> by have:=zero_lt_one.trans_le (le_max_right B (1:ℝ)); have _ : 0≤ Probe.size 0 (b-i) (ruler Mom) := apply_nonneg ..; positivity)) ht.le
    exact hA _ ht ht₂ hB₁ hsup

def SupportedAt (L : Distn Mom) (x : Mom) : Prop := ∀ f: Probe Mom, CC f → x∉ tsupport f → L f=0
noncomputable def jetDepthCoefficient (s : pinOrders) := s.sup Prod.snd
private lemma base_flatten (L : Distn Mom) (H : SupportedAt L 0) (s : pinOrders) (B : ℝ) (hB : B ≥ 0)
    (hL : ∀ f, ‖L f‖ ≤ B * pinSize s f) (hf : CC f) (he : FlatAns (2*s.sup Prod.snd + 1) 0 f) : L f=0 := by
    let k := s.sup Prod.snd
    have hb : ∀ t> (0:ℝ), L f = L (cutTest f t) := by
        intro t ht; rw [← sub_eq_zero, ← map_sub]
        refine H _ (HasCompactSupport.sub hf (cutTest_CC ..)) (notMem_tsupport_iff_eventuallyEq.mpr ((cut_exact f t ht).mono (fun x hx=> by change (f - cutTest f t) x=0; simp [hx,sub_apply])))
    have hc : Tendsto (fun t=> pinSize s (cutTest f t)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
          refine squeeze_zero' (.of_forall fun _=> pinSize_nonneg ..) (.of_forall fun t=> pin_le _ (∑ i ∈ s, Probe.size i.1 i.2 (cutTest f t)) _ (by exact Finset.sum_nonneg fun _ _ => apply_nonneg ..) (fun i hi=> Finset.single_le_sum (s:=s) (f:=fun x=> Probe.size x.1 x.2 (cutTest f t)) (fun _ _=>apply_nonneg ..) hi)) ?_
          have hi i (hi:i∈s) : Tendsto (fun t=>Probe.size i.1 i.2 (cutTest f t)) (𝓝[>]0) (𝓝 (0:ℝ)) := zero_size f he _ _ (Finset.le_sup (f:=Prod.snd) hi)
          simpa only [Finset.sum_const_zero (s:=s)] using! (tendsto_finsetSum s hi)

    have hh: Tendsto (fun t => ‖L f‖) (𝓝[>] (0:ℝ)) (𝓝 0) := squeeze_zero' (.of_forall fun _=> norm_nonneg _) ((show ∀ᶠ s in 𝓝[>] (0:ℝ), s>0 from self_mem_nhdsWithin)|>.mono fun t (ht:0<t)=> (hb t ht).symm ▸ hL (cutTest f t)) (show Tendsto (fun t => B * pinSize s (cutTest f t)) (𝓝[>]0) (𝓝 0) from by simpa using (hc.const_mul B)) -- hb ▸ changes t? fix
    exact norm_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hh)

lemma supported_bound (L : Distn Mom) (H : SupportedAt L 0) (s : pinOrders) (B : ℝ) (hB : B ≥ 0)
    (hL : ∀ g, ‖L g‖ ≤ B * pinSize s g) (he : FlatAns (2*s.sup Prod.snd + 1) 0 f) : L f=0 :=
    tendsto_nhds_unique ((L.continuous.tendsto f).comp (cutTest_limit f)) (tendsto_const_nhds.congr' ((eventually_gt_atTop (0:ℝ)).mono (fun t ht => Eq.symm (base_flatten _ L H s B hB hL (cutTest_CC ..) (cut_flat f ht he))))) -- syntax ..

end YM.Trace.Shell
