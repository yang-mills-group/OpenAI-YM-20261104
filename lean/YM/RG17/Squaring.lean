import YM.RG17.Metrics

/-!
Apply to ACTUAL built Final.s rays after Hilbert comparison.
Same polynomials. Use one-filter interactions without uniform bound n;
the elimination works because every sector is polynomial AND sees enough
of the same vacuum.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.RG17.TracePay
open Function Set Filter MeasureTheory Boundary Trace Shell Complex
open scoped Topology BigOperators ContDiff ENNReal NNReal InnerProductSpace Matrix.Norms.Frobenius
variable {n:ℕ} (w:ℕ → Trace.Shell.cell n) (b:Filter ℝ) [b.NeBot] (hb:b≤atTop) (N:ℕ)
include hb
set_option linter.unusedSectionVars false -- used in tendsto_unique etc
private lemma pullPoly (s: Finset ℕ) (d:ℕ)(hd:N ≤ n+d) (H:Tendsto (fun t:ℝ=> (t⁻¹)^N * ‖linePoly s n w t‖) b (𝓝 0)) :
    Tendsto (fun t:ℝ=> (t^(n+d))⁻¹ • linePoly s n w t) b (𝓝 0):=by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _=> norm_nonneg _) _ H
  filter_upwards [(eventually_gt_atTop (1:ℝ)).filter_mono hb] with r hr
  have hx:=zero_lt_one.trans hr
  rw [norm_smul,Real.norm_of_nonneg,inv_pow]; exact mul_le_mul_of_nonneg_right (((inv_le_inv₀ (pow_pos hx _) (pow_pos hx _)).2 (pow_le_pow_right₀ hr.le hd))) (norm_nonneg _)
  positivity
lemma sectionDegrees (s: Finset ℕ) : Tendsto (fun t:ℝ=> (t⁻¹)^N*‖linePoly s n w t‖) b (𝓝 0) →
    ∀ d ∈ s,N≤ n+d → w d=0:= by
   induction s using Finset.induction_on_max with
   | empty=> simp
   | insert d s h ih=>
     intro H m hm hm'
     have hD:= hm'.trans (show n+m ≤ n+d from Nat.add_le_add_left ((Finset.mem_insert.mp hm).elim Eq.le fun hs=>(h m hs).le) _)
     have hz:= tendsto_nhds_unique ((poly_leading w s d h).mono_left hb) (pullPoly w b hb N _ _ hD H)
     rcases Finset.mem_insert.mp hm with rfl|hm
     · exact hz
     have he t : linePoly (insert d s) n w t=linePoly s n w t:=by unfold linePoly; rw [Finset.sum_insert (fun hs=>lt_irrefl _ (h d hs)),hz,smul_zero,zero_add]
     simp_rw [he] at H; exact ih H m hm hm'
lemma sparse_char (s: Finset ℕ) (h:Tendsto (fun t:ℝ=> t⁻¹ ^ (N+1) *‖linePoly s n w t‖) b (𝓝 0)) :
   ∃ C≥(0:ℝ), (N<n → ∀ t,linePoly s n w t=0)∧ ∀ t≥1, ‖linePoly s n w t‖ ≤ C*t^N:=by
   have hw:=sectionDegrees w b hb _ s h
   let C:=∑ i∈s, ‖w i‖
   refine ⟨C,Finset.sum_nonneg (fun _ _=>norm_nonneg _),fun ht t=>Finset.sum_eq_zero (fun i hi=> by rw [hw i hi (ht.trans_le (Nat.le_add_right ..)),smul_zero]),fun t ht=>?_⟩
   unfold C linePoly; rw [Finset.sum_mul]; apply (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi=> ?_)
   rw [norm_smul, Real.norm_of_nonneg (by positivity)]
   by_cases hz:n+i ≤ N
   · rw [mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht hz) (norm_nonneg _)
   rw [hw i hi (by omega),norm_zero,mul_zero,zero_mul]

variable {m : ℕ} (f:Test4) (v:Test4→L[ℂ]Shell.Sum m) (hv:FieldImage v) (hf:CC f)
   (hq:Tendsto (fun r:ℝ=> r⁻¹^(N+1)*‖v (normalized f r)‖) b (𝓝 0))
include hv hf hq hb
lemma sector_paid (k:@Angle m (n+1)) : ∃ C≥(0:ℝ),(n+1≥N+1→ C=0)∧ ∀ t≥1,
    (∫ p, ‖componentFn k (v (normalized f t) (n+1)) p‖^2∂νpow (n+1)) ≤ C*t^(N*2):=by
   obtain ⟨q,c,hc,h⟩:= quotient_bound v hv k
   let w:= beamLip f c hc
   let s:= degrees q (n+1)
   have hs:Tendsto (fun r:ℝ=> r⁻¹^(N+1)*‖linePoly s (n+1) w r‖) b (𝓝 0):= by
      have hr:∀ᶠ t:ℝ in b,0<t:= (eventually_gt_atTop (0:ℝ)).filter_mono hb
      exact squeeze_zero' (hr.mono fun t ht=> mul_nonneg (pow_nonneg (inv_pos.mpr ht).le _) (norm_nonneg _)) (hr.mono fun t ht=> mul_le_mul_of_nonneg_left (linePoly_le f c v hv k hf hc h ht) (pow_nonneg (inv_pos.mpr ht).le _)) hq
   obtain ⟨C,hC,hz,hP⟩:=sparse_char w b hb N s hs
   by_cases he:n+1≥N+1
   · refine ⟨0,le_rfl,fun _=> rfl,fun t ht=>?_⟩
     have h:=linePoly_component f c v hv k hf hc h (zero_lt_one.trans_le ht); rw [← h,hz (by omega),norm_zero]; norm_num
   refine ⟨C^2,sq_nonneg _,fun hi=> (he hi).elim,fun t ht=>?_⟩
   rw [← linePoly_component f c v hv k hf hc h (zero_lt_one.trans_le ht), pow_mul, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hP _ ht) 2
lemma allSectorBills (n:ℕ) : ∃ C≥(0:ℝ), (n≥N+1→C=0) ∧ ∀ t≥1, ‖v (normalized f t) n‖^2 ≤ C*t^(N*2):=by
   cases n with
   | zero=>
      refine ⟨‖v f 0‖^2,by positivity,by omega,fun t ht=>?_⟩; have hx:=zero_lt_one.trans_le ht
      have h : v (normalized f t) 0 = v f 0:= Lp.ext (by
         filter_upwards [fullWave_of_CC v hv f hf 0,fullWave_of_CC v hv (normalized f t) (normalized_CC hf _) 0] with x hy hz
         rw [hy,hz,show Shell.total x=0 by simp [Shell.total],plus_normalized f hx,smul_zero])
      rw [h]; exact le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ ht)
   | succ n=>
      choose C hc hz hk using sector_paid (n:=n) b hb N f v hv hf hq
      refine ⟨∑ k:@Angle m (n+1), C k, Finset.sum_nonneg (fun k _=> hc _),fun hx=> Finset.sum_eq_zero fun k _ => hz _ hx,fun t ht=>?_⟩
      rw [assembled_sq f v hv,Finset.sum_mul]; exact Finset.sum_le_sum (fun k _=>hk k t ht)
lemma allSquared : ∃ C≥(0:ℝ), ∀ t≥1, ‖v (normalized f t)‖^2 ≤ C*t^(N*2):=by
   choose C hc hq hk using fun n=> allSectorBills b hb N f v hv hf hq n
   refine ⟨∑ i∈Finset.range (N+1), C i, Finset.sum_nonneg fun _ _=> hc _,fun t ht=> ?_⟩
   have he (z:Shell.Sum m) : ‖z‖^2=∑' n, ‖z n‖^2:=by
      convert lp.norm_rpow_eq_tsum (p:=2) (by simp) z using 2 <;> norm_num [Real.rpow_two]
   rw [he,tsum_eq_sum (s:= Finset.range (N+1)) ?_,Finset.sum_mul]; exact Finset.sum_le_sum fun k _=> hk k t ht
   intro i hi; exact le_antisymm ((hk _ _ ht).trans_eq (by simp [hq i (show i≥N+1 by simpa using hi)])) (sq_nonneg ..)
end YM.RG17.TracePay
