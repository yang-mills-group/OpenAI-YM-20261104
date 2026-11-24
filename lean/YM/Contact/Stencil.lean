import YM.Contact.Dyadic

/-! An auxiliary distributional construction at arbitrary arity. Proper collisions in one
unit annulus are filled with seminorm-bounded continuations, not (yet) with the operator
field channels. The critical central Taylor subtraction controls the outer operation even on
joint tests meeting proper diagonals. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts
open LinearMap Set Filter Function MeasureTheory
open scoped Topology ContDiff NNReal Pointwise BigOperators
variable {k:ℕ} {d:ℕ}
set_option quotPrecheck false
local notation "E" => Points k

def zoom (f:E→ℂ)(r:ℝ):E→ℂ:=fun x=> f (r • x)

def degree (k d:ℕ) := (d:ℤ)-(Module.finrank ℝ (Points k):ℕ)
lemma rank_relative_sq (k:ℕ) : Module.finrank ℝ (Points k)=4*k:= by rw [Points.flatten.toLinearEquiv.finrank_eq]; simp only [finrank_euclideanSpace,Axis,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm]
lemma degree_formula (k d:ℕ):degree k d=(d:ℤ)-4*k:=by dsimp only [degree]; rw [rank_relative_sq,Nat.cast_mul,Nat.cast_ofNat]

/-- Numerical engineering control, with fixed finite order (does not depend on ε).
`zoom` need not have any derivative bounds at a contact in the band. -/
structure Manage (f : E→ℂ)(d:ℕ) : Prop where
  cont : ContinuousOn f (airborne k)
  budget {e:ℝ}(he:0 < e){R:ℝ}(hR:0<R):∃ C:ℝ,0≤C ∧ ∀ r:ℝ,0<r → r ≤ R → Due (zoom f r) (d+1) (C*r^(-(d:ℝ)-e))

variable {f:Points k → ℂ}(H:Manage f d)
namespace Manage
include H
private lemma live' (r:ℝ)(hr : 0<r): Set.Nonempty {C:ℝ|Due (zoom f r) (d+1) C} :=
     ⟨(H.budget zero_lt_one hr).choose*r^(-(d:ℝ)-1), (H.budget zero_lt_one hr).choose_spec.2 r hr le_rfl⟩
private lemma valid (r:ℝ)(hr:0<r): ContinuousOn (zoom f r) (band k) := H.cont.comp (continuous_const_smul r|>.continuousOn) (fun _ hx=>airborne_smul hx.1 hr)

def onBand (H:Manage f d) (r:ℝ)(hr:0<r): Trial E→ₗ[ℂ] ℂ:=kernelLM (H.valid r hr) (H.live' r hr)
lemma onBand_cost {e:ℝ}(he: 0< e){R:ℝ}(hR:0<R):∃ C:ℝ,0<C ∧ ∀ r:ℝ,∀ hr:0<r, r ≤ R →∀ (φ:Trial E){B:ℝ},Major (d+1) φ B→ ‖H.onBand r hr φ‖≤C*r^(-(d:ℝ)-e)*B:=by
  obtain ⟨c,hc,hb⟩:=H.budget he hR
  refine ⟨(2*c*bandMass k)+1,by linarith only [mul_nonneg hc (bandMass_nonneg k)],?_⟩
  intro r hr hv φ B hφ; refine (kernelLM_cost _ _ _ (hb r hr hv) hφ).trans (?_)
  exact mul_le_mul_of_nonneg_right (by ring_nf; nlinarith only [Real.rpow_nonneg hr.le (-(d:ℝ)-e)] -- fix
      ) hφ.nonneg
/-- One signed summand (normal coordinates). -/
def visit (H:Manage f d) (s:ℝ)(i:ℤ): Trial E→ₗ[ℂ] ℂ:= ((radius i)^(Module.finrank ℝ E):ℂ) • (H.onBand (radius i) (radius_pos i)|>.comp (packetize E (degree k d) s (radius i)))
lemma visit_apply (s:ℝ)(i:ℤ)(φ: Trial E): visit H s i φ= ((radius i)^(Module.finrank ℝ E):ℂ) * (H.onBand (radius i) (radius_pos i) (packetize E (degree k d) s (radius i) φ)):=rfl
lemma onBand_equal (r:ℝ)(hr:0<r)(φ:Trial E)(hφ:φ∈flat k (d+1)): H.onBand r hr φ=bandAverage (zoom f r) φ:=kernelLM_flat _ _ _ hφ
-- above naming potential
end Manage

private lemma shrink_cut_scaled (s r:ℝ)(hr:0<r)(m:ℤ)(φ:Trial E): ∀ x:E,
     remainder s m (shrinking r φ) x=(r^(Module.finrank ℝ E))⁻¹ • remainder (s/r) m φ (r⁻¹ • x):=by
   intro x; rw [remainder,shrinking_apply,shrink_apply,remainder,smul_sub];congr 1
   rw [taylorCut,taylorCut]; split_ifs <;> try rw [smul_zero]
   have hf:(s/r)⁻¹*r⁻¹=s⁻¹:=by rw [inv_div,div_eq_mul_inv];field_simp
   have hc:chi s x=chi (s/r) (r⁻¹ • x):=by simp only [chi, smul_smul,hf]
   simp only [shrinking_fun,polynomial,jet_shrink,smul_zero,Finset.smul_sum,hc];apply Finset.sum_congr rfl; intro _ _; exact smul_comm ..

private lemma eqscaled {r ℓ:ℝ}(hr:0<r){s:ℝ}{φ:Trial E}{m:ℤ}:
     packetize E m s ℓ (shrinking r φ) = ((r^(Module.finrank ℝ E))⁻¹:ℂ) • (packetize E m (s/r) (ℓ/r) φ):=by
   ext1 x; change packet E m s _ _ x= ((r^(Module.finrank ℝ E))⁻¹:ℂ) • packet E m (s/r) (ℓ/r) φ x; simp only [packet,shrink_cut_scaled s r hr]; rw [smul_comm (filterU E x) (r^Module.finrank ℝ E)⁻¹,smul_smul (r⁻¹) ℓ,
       ← Complex.ofReal_pow,← Complex.ofReal_inv, inv_mul_eq_div]
   exact RCLike.real_smul_eq_coe_smul (K:=ℂ) _ _

private lemma zero_far (s:ℝ)(hs:0<s)(R:ℝ){r ℓ:ℝ}(hr:0<r)(hr':r ≤ 1) (hℓ: 4*s+2*R+1<ℓ)(hR:0<R){φ:Trial E}{m:ℤ}(hφ:support ⇑φ ⊆ Metric.closedBall 0 R):packetize E m (s/r) (ℓ/r) φ=0:=by
   ext x; change packet E m _ _ φ x=0
   by_cases hx:filterU _ x=0
   · rw [packet,hx,zero_smul]
   have ht : 1/2 ≤ ‖x‖:=le_of_not_gt fun h=> hx (filter_near E x h)
   have hℓ':0 < ℓ:=by linarith
   have hrf : r⁻¹*ℓ=ℓ/r:=inv_mul_eq_div r ℓ
   have he:ℓ/2 ≤ ℓ/r * ‖x‖ := by
       rw [← hrf, mul_assoc]; apply le_inv_mul_iff₀ hr |>.mpr
       linarith only [mul_le_of_le_one_right (by positivity:0 ≤ ℓ/2) hr', mul_le_mul_of_nonneg_left ht hℓ'.le]
   have hp : φ ((ℓ/r) • x)=0:= notMem_support.mp (fun hu=> by
      have hv:= mem_closedBall_zero_iff.mp (hφ hu)
      rw [norm_smul_of_nonneg (by positivity)] at hv; nlinarith only [hs,he,hℓ,hv,hR])
   simp only [packet, remainder,taylorCut,hp, chi_lt_zero (s/r) (by positivity) ((ℓ/r) • x) (by
       rw [norm_smul_of_nonneg (by positivity)]; rw [← mul_div_assoc, ← mul_div_right_comm]; exact (div_lt_div_iff_of_pos_right hr).mpr (by nlinarith))]; split_ifs <;> simp

private lemma redistribution (r q:ℝ)(hr:0<r)(hq:0<q)(d m n e:ℝ)(hm:m=d-n) :
   q^n*(q*r)^(-d-e)=r^(-d-e) * q^(-m-e):=by
     rw [Real.mul_rpow hq.le hr.le, ← mul_assoc,← Real.rpow_add hq]; have hx:n+(-d-e)=-m-e:=by linarith
     rw [hx,mul_comm]
-- include H in envelope
lemma Manage.preview (s:ℝ)(hs:0<s) (R:ℝ)(hR:1≤ R){e:ℝ}(he:0<e)(he':e<1):
   ∃ C:ℝ,0≤ C ∧ ∀ (r:ℝ)(_hr:0<r),r ≤ min 1 s → ∀ {φ:Trial E}{B:ℝ}, support ⇑φ ⊆ Metric.closedBall 0 R → Major (d+1) φ B → ∀ i,
     ‖H.visit s i (shrinking r φ)‖ ≤
       if (radius i/r ≤ 1/4) then (C * r^(-(d:ℝ)-e) * B) * (radius i/r)^((degree k d + 1 : ℤ).toNat-(degree k d:ℝ)-e)
         else (C*r^(-(d:ℝ)-e)*B) * (radius i/r)^(-e):=by
   have hR':0 < R:= lt_of_lt_of_le zero_lt_one hR
   obtain ⟨c,hc,hb⟩:=H.onBand_cost he (show 0 < 4*s+2*R+1 by linarith)
   let m:=degree k d; let l:= (m+1).toNat
   have hj:l ≤ d+1:=by dsimp only [l,m,degree]; omega
   obtain ⟨a,ha,ha'⟩:=small_packet E m (d+1)
   obtain ⟨b,hbp,b'⟩:=large_packet E m (d+1) R hR
   let A:=max a b; have ha'':a ≤ A:= le_max_left ..; have hA:0≤A:=ha.le.trans ha''; have hb':b≤ A:=le_max_right ..
   refine ⟨c*A,mul_nonneg hc.le hA,fun r hr hr' φ B hφ hφ' i=>?_⟩
   let t:=radius i; let q:=t/r; let D:=Module.finrank ℝ E
   let N:= H.onBand t (radius_pos i); let ψ:=packetize E m (s/r) q φ
   have ht:t>0:=radius_pos i; have hq:0<q:= div_pos ht hr; have heq:q*r=t:=div_mul_cancel₀ t hr.ne'; have hm:(m:ℝ)=(d:ℝ)-(D:ℝ):= Int.cast_sub .. -- fix simp
   rw [visit_apply]; change ‖(t^D:ℂ)*N (packetize E m s _ (shrinking r φ))‖ ≤ _ ; rw [eqscaled hr,map_smul,norm_mul,norm_smul]
   rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg ht.le _),← Complex.ofReal_pow,← Complex.ofReal_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
   by_cases ht':4*s+2*R+1<t
   · rw [zero_far s hs R hr (hr'.trans (min_le_left ..)) ht' hR' hφ,map_zero, norm_zero, mul_zero,mul_zero]
     split_ifs <;> positivity [hφ'.nonneg] -- rpow
   have hv (u:ℝ)(hψ : Major (d+1) ψ (A*B*q^u)):
          q^D*‖N ψ‖ ≤ c*A*r^(-(d:ℝ)-e)*B*q^(u-(m:ℝ)-e):=by
      apply (mul_le_mul_of_nonneg_left (hb _ _ (not_lt.mp ht') _ hψ) (pow_nonneg hq.le _)).trans
      calc q^D*(c*t^(-(d:ℝ)-e)*(A*B*q^u))=(q^D*t^(-(d:ℝ)-e))*(c*A*B)*q^u:=by ring
           _=(r^(-(d:ℝ)-e)*q^(-(m:ℝ)-e))*(c*A*B)*q^u:=by rw [← Real.rpow_natCast q,← heq,redistribution r q hr hq _ _ _ _ hm]
           _ = c*A*r^(-(d:ℝ)-e)*B*q^(u-(m:ℝ)-e) := by rw [show u-(m:ℝ)-e= (-(m:ℝ)-e)+u from by ring,Real.rpow_add hq]; ring
           _ ≤ _ := le_refl _
   have hd':Major (max (d+1) (m+1).toNat) φ B:=hφ'.weaken (max_le le_rfl hj) le_rfl
   change t^D*((r^D)⁻¹ * ‖N ψ‖) ≤ if (q ≤ 1/4) then (c*A * r^(-(d:ℝ)-e) * B) * q^((degree k d + 1).toNat-(degree k d:ℝ)-e) else (c*A*r^(-(d:ℝ)-e)*B) * q^(-e)
   rw [← mul_assoc,show t^D*(r^D)⁻¹ = q^D from (by dsimp [q];rw [_root_.div_pow, _root_.div_eq_mul_inv])]
   have hs':1 ≤ s/r:=(one_le_div hr).mpr (hr'.trans (min_le_right ..))
   split_ifs with h
   · apply hv
     rw [Real.rpow_natCast q]
     exact (ha' hs' hq h hd').weaken le_rfl (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha'' hφ'.nonneg) (by positivity))
   exact (hv (m:ℝ) ((b' _ (div_pos hs hr) _ (not_le.mp h).le hφ hd').weaken le_rfl (by rw [mul_right_comm]; apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb' hφ'.nonneg) (Real.rpow_nonneg hq.le _)))).trans (by simp)
end YM.Contacts
