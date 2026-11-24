import YM.Frontier6.Normal.PlanSize

/-!
# Taylor shell charges near and far

The critical estimate is strong in full test derivatives of *any* fixed
order. Pay the cost in incoming shell once. Tail power never grows with order j.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Normal
open Function Filter Set MeasureTheory Metric
open scoped Topology ContDiff BigOperators Classical
variable {X Y:Type*}[NormedAddCommGroup X][InnerProductSpace ℝ X][FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {s t P Q R r:ℝ} {f: Full X} {L:Set X} {j m:ℕ}
omit [FiniteDimensional ℝ X] in
lemma develop {f:X→Y}(h:Smooth f)(hr:0 ≤ r)(hs:0<s)(hp:P≥0)(H:Estimate m s f (closedBall (0:X) (2*r)) P)(hv:∀ j<m, iteratedFDeriv ℝ j f (0:X)=0) (he:j≤m): ∀ x∈ closedBall (0:X) (2*r),
     ‖iteratedFDeriv ℝ j f x‖ ≤ (2*r)^(m-j)* (P / s^m):=by
   generalize hy:m-j=n
   induction n generalizing j with
   | zero=>
      have hh:m=j:=by omega
      subst m; intro x hx; rw [pow_zero,one_mul,le_div_iff₀ (pow_pos hs _),mul_comm]; exact H _ le_rfl x hx
   | succ n ih=>
      have hj:j<m:=by omega
      specialize ih (show j+1 ≤ m from hj) (show m-(j+1)= n by omega)
      intro x hx
      let L:=iteratedFDeriv ℝ j f; let B:=(2*r)^n*(P/s^m)
      have hk(z): DifferentiableAt ℝ L z:= (charge_smooth h (j+1)).contDiffAt.differentiableAt_iteratedFDeriv (show (j:WithTop ℕ∞)< ((j+1:ℕ):WithTop ℕ∞) from Nat.cast_lt.mpr (by omega))
      have hl:= (convex_closedBall (0:X) (2*r)).norm_image_sub_le_of_norm_fderiv_le (f:=L) (fun z _=>hk z) (fun z hz=> le_trans (le_of_eq norm_fderiv_iteratedFDeriv) (ih z hz)) (show (0:X) ∈ closedBall 0 (2*r) from by simp [hr]) hx
      rw [show L 0=0 from hv j hj,sub_zero,sub_zero] at hl; refine hl.trans (le_trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) (show 0 ≤ B by unfold B; positivity)) (le_of_eq ?_)); ring

omit [FiniteDimensional ℝ X] in
lemma smaller_price {f:X→ Y}(hr:0<t)(hs:t≤s)(hp:0 ≤ P)(h:Smooth f)(H:Estimate (j+m) s f (closedBall (0:X) (2*s)) P)(hv:∀ i<m,iteratedFDeriv ℝ i f (0:X)=0):
     Estimate j t f (closedBall (0:X) (2*t)) ((2:ℝ)^m*P*(t/s)^m):=by
   have hh:0<s:=lt_of_lt_of_le hr hs
   let α:=t/s; have hα:0 ≤ α:=div_nonneg hr.le hh.le; have hβ:α ≤ 1:=(div_le_one hh).mpr hs
   have hY: closedBall (0:X) (2*t) ⊆ closedBall 0 (2*s):= closedBall_subset_closedBall (by linarith); have hU:=H.subset hY
   intro i hi x hx
   rcases le_total i m with he|he
   · have h':= develop h hr.le hh hp (hU.lower (show m ≤ _ by omega)) hv he x hx; refine le_trans (mul_le_mul_of_nonneg_left h' (pow_nonneg hr.le _)) ?_
     have hA:t^i*t^(m-i)=t^m:=by rw [← pow_add, Nat.add_sub_of_le he]
     rw [mul_pow, show t^i * ((2^ (m-i)*t^(m-i))*(P/s^m))= ( (2:ℝ)^(m-i))*P * (t^i*t^(m-i))/s^m by ring,hA,mul_div_assoc, div_pow] -- check
     exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hp) (by positivity)
   have hT: t^i=α^i*s^i:=by rw [← mul_pow]; simp only [α,div_mul_cancel₀ _ hh.ne']
   rw [hT,mul_assoc]; refine le_trans (mul_le_mul_of_nonneg_left (hU i (by omega) x hx) (pow_nonneg hα _)) ?_
   rw [mul_comm (α^i)]; exact mul_le_mul (le_mul_of_one_le_left hp (one_le_pow₀ (by norm_num))) (pow_le_pow_of_le_one hα hβ he) (pow_nonneg hα _) (mul_nonneg (by positivity) hp)

lemma left_near (m j:ℕ)(R:ℝ)(hR:1≤R):∃ B:ℝ,0 ≤ B ∧ ∀ t:ℝ,0<t→ ∀ s:ℝ,t ≤ R*s→ ∀ r:ℝ, 0<r → r ≤ t → ∀ (φ:Full X)(P:ℝ), Charge (j+m+1) t (φ:X→ℂ) P →
   Estimate j r (leftOut s m φ : X→ℂ) (closedBall (0:X) (2*r)) (B*P*(r/t)^(m+1)):=by
   let k:=j+(m+1); obtain ⟨A,hA,hc⟩:= plan_estimate (X:=X) k m 2 (by norm_num); obtain ⟨C,hC,H⟩:= shrink_charge (X:=X) k
   let D:=1+(2:ℝ)^k*(R^k*C)*A; have hD:0 ≤ D:=by
     have hv:0 ≤ R:=by linarith only [hR]
     unfold D; positivity -- newline
   refine ⟨2^(m+1)*D,mul_nonneg (by positivity) hD,fun t ht s hs r hr hy φ P h => ?_⟩
   have hR':0 < R:=zero_lt_one.trans_le hR
   have hs':0 < s:=pos_of_mul_pos_right (ht.trans_le hs) hR'.le
   rw [Nat.add_assoc] at h; have h1:=(H s hs'); let U:=leftOut s m φ; let W:=closedBall (0:X) (2*t); have hp:=Charge.nonneg h
   have hh: Estimate k t U W (D*P):=by
      have ht':= Estimate.subset (Estimate.scale_up h1 hs'.le ht.le hC hR hs) (subset_univ W)
      have hV: Estimate k t (plan m (φ:X→ℂ)) W (A*P):= by simpa using hc (φ:X→ℂ) t P t 1 ht ht le_rfl (by simp) (Estimate.lower h (by omega))
      have hL:= ht'.mul hV (mul_nonneg (pow_nonneg hR'.le _) hC) (mul_nonneg hA hp) ht.le (shrink X s).contDiff (plan_smooth ..)
      rw [← portion_act] at hL
      have hu:D*P=P+(2:ℝ)^k * (R^k*C)*(A*P):=by unfold D; ring
      rw [hu]; exact Estimate.sub (Estimate.subset h (subset_univ W)) hL φ.contDiff (portion s m φ).contDiff ht.le
   have hv(i:ℕ)(hi:i<m+1): iteratedFDeriv ℝ i U (0:X) =0:= by
      change iteratedFDeriv ℝ i ((φ:X→ℂ)-(portion s m φ:X→ℂ)) (0:X)=0
      rw [iteratedFDeriv_sub_apply (charge_smooth φ.contDiff i|>.contDiffAt) (charge_smooth (portion s m φ).contDiff i|>.contDiffAt), portion_same_jet hs' m i φ (by omega),sub_self]
   rw [mul_assoc _ D]; exact smaller_price hr hy (mul_nonneg hD hp) U.contDiff hh hv

lemma rings_inside {x:X}(h:x∈Ringed X s): x∈closedBall (0:X) (2*s):=mem_closedBall_zero_iff.mpr h.2
lemma packet_coarse (h:Charge j t (f:X→ℂ) P)(ht:0<t)(hr:0 ≤ r)(hR:1 ≤ R)(hp:Fits (R*t) f): Estimate j r f (Ringed X r) ((2*R)^j*P):=by
   by_cases he:r ≤ 2*R*t
   · exact Estimate.subset (Estimate.scale_up h ht.le hr (Charge.nonneg h) (show 1≤ 2*R by linarith only [hR]) he) (subset_univ _)
   have hv:=Charge.nonneg h; have hl:0 ≤ R:= zero_le_one.trans hR
   intro i hi x hx
   rw [show iteratedFDeriv ℝ i f x=0 from image_eq_zero_of_notMem_tsupport (fun hy=> ?_),norm_zero,mul_zero]; positivity
   have heq:R*t<‖x‖:= lt_of_lt_of_le (by linarith only [lt_of_not_ge he]) hx.1; exact heq.not_ge (mem_closedBall_zero_iff.mp (hp (tsupport_iteratedFDeriv_subset i hy)))
lemma plan_coarse (m j:ℕ): ∃ B:ℝ,0 ≤ B∧ ∀ t s r:ℝ,0<t→0<s→t≤r→ ∀ (f:Full X)(P:ℝ),Charge m t (f:X→ℂ) P →
    Estimate j r (portion s m f : X→ℂ) (Ringed X r) (B*P*(r/t)^m):=by
   obtain ⟨C,hC,hX⟩:= plan_estimate (X:=X) j m 2 (by norm_num); obtain ⟨D,hD,H⟩:=shrink_charge (X:=X) j
   refine ⟨2^j*((2*2)^j*D)*C,by positivity,fun t s r ht hs hr f P h=>?_⟩
   have ht':=lt_of_lt_of_le ht hr; have hz:0 ≤ r/t:= div_nonneg ht'.le ht.le; have hh:=Charge.nonneg h
   have hv:=packet_coarse (H s hs) hs ht'.le (R:=2) (by norm_num) (shrink_fits hs)
   have hw:=hX (f:X→ℂ) t P r (r/t) ht ht' ((one_le_div ht).2 hr) (by rw [div_mul_cancel₀ _ ht.ne']) h
   have hl:=hv.mul (hw.subset (fun _=> rings_inside)) (by positivity) (by positivity) ht'.le (shrink X s).contDiff (plan_smooth ..)
   rw [portion_act]; exact Estimate.down_cost hl (le_of_eq (by ring))
lemma left_coarse (m j:ℕ)(R:ℝ)(hR:1≤ R) : ∃ B:ℝ,0 ≤ B∧ ∀ t s r:ℝ,0<t→0<s→t≤r→ ∀ (f:Full X)(P:ℝ), Fits (R*t) f → Charge (j+m) t (f:X→ℂ) P →
   Estimate j r (leftOut s m f : X→ℂ) (Ringed X r) (B*P*(r/t)^m):=by
   obtain ⟨C,hC,h⟩:=plan_coarse (X:=X) m j; have hR':0 ≤ R:=zero_le_one.trans hR
   refine ⟨(2*R)^j+C,by positivity,fun t s r ht hs he f P hF hp=>?_⟩
   have hv:=h t s r ht hs he f P (Estimate.lower hp (by omega)); have hx:=Charge.nonneg hp
   rw [add_mul,add_mul]; exact (Estimate.sub (Estimate.down_cost (packet_coarse (j:=j) (Estimate.lower hp (by omega)) ht (ht.le.trans he) hR hF) (le_mul_of_one_le_right (by positivity:0 ≤ (2*R)^j * P) (one_le_pow₀ ((one_le_div ht).2 he)))) hv f.contDiff (portion s m f).contDiff (ht.le.trans he) : Estimate j r _ (Ringed X r) _)
end YM.Frontier6.Normal
