import YM.Contact.Raw

/-! Identification on genuine strict products, for positive normal dimension. -/
noncomputable section
set_option autoImplicit false
namespace YM.Contacts
open Set Metric Filter Function MeasureTheory LinearMap
open scoped Topology ContDiff BigOperators Pointwise

variable {k d:ℕ}
set_option quotPrecheck false
local notation "E"=>Points k
variable {f:Points k→ℂ}{φ:Trial (Points k)}
variable (H:Manage f d)
namespace Manage

private lemma erase {g:E→ℂ} {x:E} (hx:x∉tsupport g):g =ᶠ[𝓝 x] (fun _=>0):= by filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hx] with y hy using image_eq_zero_of_notMem_tsupport hy

private lemma strictContinuous (H:Manage f d) (h: tsupport ⇑φ ⊆ airborne k): Continuous (f*(⇑φ)) := continuous_iff_continuousAt.mpr (fun x=>by
   by_cases hx:x∈airborne k
   · exact ((H.cont.continuousAt ((airborne_open k).mem_nhds hx)).mul φ.continuous.continuousAt)
   exact continuousAt_const.congr ((erase (show x∉tsupport (φ:Points k→ℂ) from fun hr=>hx (h hr))|>.mono fun y hy=>by rw [show (f*(φ:Points k→ℂ)) y=f y*φ y from rfl,hy,mul_zero])))

variable (hk:1≤ k)(h:tsupport ⇑φ⊆ airborne k)
include hk h
private lemma whole {s:ℝ}{m:ℤ}: remainder s m ⇑φ=φ:= by
  have he := (erase (show (0:E) ∉ tsupport (φ:Points k→ℂ) from fun hx=> not_lt_of_ge (zero_gap (k:=k) hk) (gap_pos 0 (h hx))))
  funext x; rw [remainder,taylorCut]; suffices polynomial m.toNat φ 0 x=0 from by rw [this]; split <;> simp
  exact Finset.sum_eq_zero (fun i hi=>by dsimp only [jet]; simp only [(he.iteratedFDeriv ℝ i).eq_of_nhds, iteratedFDeriv_fun_zero,Pi.zero_apply,_root_.zero_apply,smul_zero])

private lemma packet_flat (s:ℝ)(r:ℝ)(hr:0<r) : packetize _ (degree k d) s r φ∈flat k (d+1):=by
  intro i hi x hx
  have he: (fun y:E=>packetize _ (degree k d) s r φ y)=ᶠ[𝓝 x] 0 :=by
    have he' := (erase (show r • x∉tsupport (φ:Points k→ℂ) from fun ht=>hx (inv_smul_smul₀ hr.ne' x ▸ airborne_smul (h ht) (inv_pos.mpr hr))))
    have ht:=he'.comp_tendsto (continuous_const_smul r|>.tendsto x)
    exact ht.mono fun y hy=>by dsimp only [Function.comp_apply] at hy;change packet E (degree k d) s r φ y=(0:ℂ);rw [packet,whole hk h,hy,smul_zero]
  change iteratedFDeriv ℝ i (fun y=>packetize E (degree k d) s r φ y) x=0
  rw [(he.iteratedFDeriv ℝ i|>.eq_of_nhds)]; rw [iteratedFDeriv_zero,Pi.zero_apply]

private def integrand (f:E→ℂ)(φ:E→ℂ)(r:ℝ)(x:E):=filterU E (r⁻¹ • x) • (f x*φ x)

theorem visit_whole (H:Manage f d)(s:ℝ)(i:ℤ) :
    visit H s i φ=∫ x, filterU E ((radius i)⁻¹ • x) • (f x*φ x):=by
  let t:=radius i; have ht:=radius_pos i; let g:=integrand f φ t
  change visit H s i φ=∫ x,g x
  rw [visit_apply,onBand_equal ..];swap;· exact packet_flat hk h s _ ht
  have he(x:E) : (band k).indicator (zoom f t) x * (packetize _ (degree k d) s t φ x) = g (t•x):=by
    simp only [g,integrand,packetize_apply,packet,whole hk h]
    rw [inv_smul_smul₀ ht.ne']
    by_cases h'ψ:φ (t•x)=0
    · rw [h'ψ,mul_zero,smul_zero,mul_zero]
    by_cases h'x:filterU E x=0
    · rw [h'x,zero_smul,zero_smul,mul_zero]
    have hu(x:E)(hx:filterU E x≠0): x∈norm ⁻¹' Ioo (1/2:ℝ) 4:= by
       obtain ⟨hp,hq⟩:= Classical.byContradiction (fun H=>hx (filter_support E x H))
       have hs':‖x‖≠1/2:=fun hf=> hx (by rw [filterU,chi_one zero_lt_one _ (by linarith),chi_one zero_lt_one _ (by rw [norm_smul_of_nonneg (by norm_num:(0:ℝ)≤2)];linarith),sub_self])
       exact ⟨lt_of_le_of_ne hp hs'.symm, by linarith only [hq]⟩
    have hh:x∈band k:=⟨inv_smul_smul₀ ht.ne' x ▸ airborne_smul (h (subset_tsupport φ (mem_support.mpr h'ψ))) (inv_pos.mpr ht),hu x h'x⟩
    rw [indicator_of_mem hh];change f (t•x)*((_:ℝ) • _)=filterU E x • _; exact ((mul_smul_comm _ _ _))
  change (t ^ Module.finrank ℝ E:ℂ)*(∫ x,(band k).indicator (zoom f t) x*(packetize _ (degree k d) s t φ x)) = ∫x,g x
  simp_rw [he]
  norm_cast
  rw [← Complex.real_smul,Measure.integral_comp_smul_of_nonneg _ g t (hR:=ht.le),smul_inv_smul₀ (pow_pos ht _).ne']

omit hk in
private lemma integrand_integrable (H:Manage f d)(i:ℤ): Integrable (integrand f φ (radius i)) := by
  have hi:Continuous (fun x:E=> integrand f φ (radius i) x) := ((filter_smooth _).continuous.comp (continuous_const_smul _)).smul (strictContinuous H h)
  let g : E→ ℝ:=fun x=> filterU E ((radius i)⁻¹ • x)
  have hc: HasCompactSupport (g • (f*(⇑φ))) := φ.hasCompactSupport.mul_left.smul_left
  apply Continuous.integrable_of_hasCompactSupport hi; exact hc

lemma envelope_compact : ∃ l u:ℤ,l ≤ u ∧∀ x, φ x≠0 → 2*radius l<‖x‖ ∧ ‖x‖<radius u/2:=by
   obtain ⟨R,hR,hR'⟩:=φ.hasCompactSupport.isBounded.exists_pos_norm_le
   have he:=erase (show (0:E)∉tsupport (φ:Points k→ℂ) from fun hx=>not_lt_of_ge (zero_gap hk) (gap_pos 0 (h hx)))
   have hh : {x | φ x=0}∈𝓝 (0:E) := by filter_upwards [he] with x hx using hx
   obtain ⟨δ,hδ,hp⟩:=Metric.mem_nhds_iff.mp hh
   have ht:0 < Real.log 2:=Real.log_pos one_lt_two
   obtain ⟨l',hl'⟩:= exists_int_lt (min 0 (Real.log (δ/2)/Real.log 2))
   obtain ⟨u',hu'⟩:=exists_int_gt (max 0 (Real.log (R*2)/Real.log 2))
   obtain ⟨hz,hL⟩:=lt_min_iff.mp hl'; obtain ⟨hq,hU⟩:=max_lt_iff.mp hu'
   have hel:= (Real.zpow_lt_iff_lt_log zero_lt_two (half_pos hδ)).2 ((lt_div_iff₀ ht).1 hL)
   have heu:= (Real.lt_zpow_iff_log_lt (by positivity) zero_lt_two).2 ((div_lt_iff₀ ht).1 hU)
   exact ⟨l',u',by exact_mod_cast (by linarith only [hz,hq] : (l':ℝ)≤(u':ℝ)),fun x hx=> by
      change 2*(2:ℝ)^l' < ‖x‖∧‖x‖<(2:ℝ)^u'/2
      have hδ':¬ ‖x‖<δ:=fun h=> hx (hp (mem_ball_zero_iff.mpr h))
      have hr:=hR' x (subset_tsupport _ (Function.mem_support.mpr hx))
      constructor <;> linarith⟩

omit hk h in
private lemma step_identity (x:E)(i:ℤ): filterU E ((radius i)⁻¹ • x) = chi (radius i) x-chi (radius (i-1)) x:=by
    simp only [filterU,chi_len (radius i),chi_len (radius (i-1)),smul_smul]
    rw [show (radius (i-1))⁻¹=(2:ℝ)*(radius i)⁻¹ from ?_]
    have hQ:radius (i-1)=radius i*2⁻¹:=by change (2:ℝ)^_= _; rw [zpow_sub₀ (by norm_num),div_eq_mul_inv,zpow_one]; rfl
    rw [hQ,mul_inv_rev,inv_inv]

omit hk h in
private lemma disappears (l u i:ℤ)(hi:i∉ Finset.Icc l u)(x:E)(hh: 2*radius l≤‖x‖)(h':‖x‖<radius u/2) : filterU E ((radius i)⁻¹ • x) = 0:=by
     have hz:=radius_pos i; refine filter_support E _ (fun hw=> ?_)
     change 1/2 ≤ ‖(radius i)⁻¹ • x‖ ∧ ‖(radius i)⁻¹ • x‖ ≤ 2 at hw
     rw [norm_smul_of_nonneg (inv_pos.mpr hz).le] at hw
     have hz':i < l ∨ u < i := by by_contra! hn; exact hi (Finset.mem_Icc.mpr ⟨hn.1,hn.2⟩)
     rcases hz' with hl|hr
     · have he:= (zpow_lt_zpow_right₀ (show 1<(2:ℝ) from one_lt_two) hl)
       have hw':= (inv_mul_le_iff₀ hz).mp hw.2
       dsimp only [radius] at *;linarith only [he,hh,hw']
     have hu:= (zpow_lt_zpow_right₀ (show 1<(2:ℝ) from one_lt_two) hr)
     have hw':= (le_inv_mul_iff₀ hz).mp hw.1
     dsimp only [radius] at *; linarith only [hu,hw',h']

omit hk h in
private lemma end_sum (q:ℤ→ℂ)(l u:ℤ)(hu:l≤u): (∑ i∈Finset.Icc l u,(q i-q (i-1)))=q u-q (l-1):=by
   induction u, hu using Int.leInduction
   case base=>simp
   case succ u hu ih=>
       have hh: Finset.Icc l (u+1)=insert (u+1) (Finset.Icc l u):= by ext; simp; omega
       have hi: u+1∉Finset.Icc l u:=fun h=> by simp only [Finset.mem_Icc] at h; omega
       rw [hh,Finset.sum_insert hi,ih,add_sub_cancel_right]; ring

omit hk h in
lemma allocation (y:E) (l u:ℤ)(hl:l≤u)(H :2*radius l ≤ ‖y‖)(h':‖y‖≤radius u/2) (f:ℂ):
   (∑ i∈Finset.Icc l u,(filterU E ((radius i)⁻¹ • y) • f))=f:=by
    simp_rw [step_identity]; rw [show (fun i=>(chi (radius i) y-chi (radius (i-1)) y) • f)= (fun i=> chi (radius i) y • f-chi (radius (i-1)) y • f) from funext (fun i=>sub_smul ..)]
    rw [end_sum (fun i=> chi (radius i) y • f) _ _ hl]
    rw [chi_one (radius_pos u) _ (by linarith only [h',radius_pos u])]
    have hh: chi (radius (l-1)) y=0:=chi_lt_zero _ (radius_pos _) _ (by dsimp only [radius] at H ⊢;linarith only [H,zpow_lt_zpow_right₀ (show 1<(2:ℝ) from one_lt_two) (show l-1<l by omega)])
    rw [hh,zero_smul,one_smul,sub_zero]

include H
lemma numerical_extends (s:ℝ)(hs:0<s): numerical H s hs φ=∫ x, f x*φ x:=by
   classical
   obtain ⟨l,u,hl,h'⟩:=envelope_compact hk h
   let a:=Finset.Icc l u; have hstep(i:ℤ):visit H s i φ= ∫x,(integrand f φ (radius i)) x:=visit_whole hk h H s i
   have outside(i:ℤ)(hi:i∉ a): integrand f φ (radius i)=fun _=>0:= by
      funext x; specialize h' x; by_cases hp:φ x=0; simp only [integrand, hp, mul_zero, smul_zero]
      rw [integrand,disappears _ _ _ hi _ (h' hp).1.le (h' hp).2,zero_smul]
   have sum_eq(x:E):(∑ i∈a, integrand f φ (radius i) x)=f x*(φ x):=by
      by_cases hp:φ x=0; simp only [integrand, hp,mul_zero, smul_zero, Finset.sum_const_zero]
      obtain ⟨htx,hwx⟩:=h' x hp;exact (allocation x _ _ hl htx.le hwx.le (f x*φ x))
   calc numerical H s hs φ = ∑ i∈a, ∫ x,integrand f φ (radius i) x := (numerical_apply ..).trans ((tsum_eq_sum (s:=a) (fun i hi=>by rw [hstep i, outside i hi];simp)).trans (Finset.sum_congr rfl fun i _=>hstep i))
        _ = ∫ x, ∑ i∈a, integrand f φ (radius i) x:=(integral_finsetSum _ (fun i _=>integrand_integrable h H i)).symm
        _ = _:= by simp only [sum_eq]

end Manage
end YM.Contacts
