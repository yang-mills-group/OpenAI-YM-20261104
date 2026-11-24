import YM.Pert.Kinetic.Cap
/-! Quantitative kinetic uniqueness on the zero-flag sector (sufficient for scalar
and kinetic readout on lawful trunks prior to attachment of secondary soft
absolutes/flags). Adapt PERT Branch/Cap. This lemma would not control the
activity norms of the common estimates; working below with exact flags,
secondary soft costs, BudgetHit. Flat error will be charged
before any high-order loop recalibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Recoil
open Pert.Kinetic Pert
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {n : Side} {G : Gauge} {σ C Λ δ z σ' C' Λ' δ' z' : ℝ}

abbrev Renew (R W: Rep G n): Prop := ∀ U, flags R.p.threshold U=∅ → flags W.p.threshold U=∅ → R.eval U=W.eval U
variable (R W : Rep G n) (hG : G.Simple) (hR : R.Lawful σ C Λ δ z) (hW : W.Lawful σ' C' Λ' δ' z') (hn : 4 ≤ n.val)

include hG hn hR
private lemma control {c : G.Color} (hc : ‖c‖=1) : |(∑ b:Bool, meterK R (rowWave c b)) - R.beta/2*(Fintype.card (Site n))*(4*Real.sin (Full.mesh n/2)^2)| ≤ Fintype.card (Site n)*Full.mesh n^3*billTotal R.p σ C Λ R.beta δ := by
   simp_rw [meterK,Finset.sum_add_distrib,←Finset.sum_div];rw [add_sub_right_comm]
   refine (abs_add_le ..).trans ?_
   have hb:= sum_rates hR.paths hn hc R.beta
   have he(b:Bool):= frequencyE (n:=n) hR.labels hG c hc b 0 1 hn
   rw [Fintype.sum_bool (f:=fun b:Bool => Eread (A:=R.activities) (rowWave c b)),abs_div,abs_of_pos (zero_lt_two (α:=ℝ))] -- f syntax
   apply (add_le_add hb (div_le_div_of_nonneg_right ((abs_add_le ..).trans (add_le_add (he true) (he false))) zero_le_two)).trans_eq; unfold billTotal;ring

include hW
omit hG hR hW hn in
lemma amount {t:ℝ} {u : Directions G n} (hrad : (Renew R W)) (h : flags R.p.threshold (AnalyticBridge.VerifiedReset.line u t)=∅) (e : flags W.p.threshold (AnalyticBridge.VerifiedReset.line u t)=∅) :
    measuredAction R (AnalyticBridge.VerifiedReset.line u t) - measuredAction W (AnalyticBridge.VerifiedReset.line u t)=(R.v-W.v)* (Fintype.card (Site n) : ℝ) := by
    have ht := hrad _ h e
    simp only [RG.Rep.eval,Activities.gas_one _ _ h,Activities.gas_one _ _ e,mul_one,RG.Rep.exponent] at ht
    apply Real.exp_injective at ht
    unfold measuredAction; linarith only [ht]
lemma priced (c : G.Color) (hc : ‖c‖=1) (b:Bool) (he:(Renew R W)) : meterK R (rowWave c b)=meterK W (rowWave c b) ∧ R.v=W.v := by
    have hr:= unscale R hR c hc b hG hn
    have hw:= unscale W hW c hc b hG hn
    have hz := (hr.mul (show Tendsto (fun t:ℝ=>t^2) (𝓝[≠] 0) (𝓝 0) from by simpa using (tendsto_id (x:=𝓝 (0:ℝ)) |>.pow 2 |>.mono_left nhdsWithin_le_nhds))).sub (hw.mul (show Tendsto (fun t:ℝ=>t^2) (𝓝[≠] 0) (𝓝 0) from by simpa using (tendsto_id (x:=𝓝 (0:ℝ)) |>.pow 2 |>.mono_left nhdsWithin_le_nhds)))
    let v : Directions G n := rowWave c b; let U:=AnalyticBridge.VerifiedReset.line v
    have ht : ∀ᶠ t:ℝ in 𝓝[≠] 0, measuredAction R (U t) - measuredAction W (U t)=(R.v-W.v)*(Fintype.card (Site n):ℝ) := by
       filter_upwards [((rays_free R.p.threshold R.p.threshold_pos v).filter_mono nhdsWithin_le_nhds), ((rays_free W.p.threshold W.p.threshold_pos v).filter_mono nhdsWithin_le_nhds)] with t h1 h2
       exact amount R W he h1 h2
    have hv0:(R.v-W.v)*(Fintype.card (Site n):ℝ)=0:= by
       apply (tendsto_nhds_unique (l:=𝓝[≠] (0:ℝ)) tendsto_const_nhds ?_)
       rw [mul_zero,mul_zero,sub_self] at hz; refine hz.congr' ?_
       filter_upwards [ht, (self_mem_nhdsWithin : ∀ᶠ t:ℝ in 𝓝[≠] 0, t≠0)] with t hT ht'; change measuredAction R (U t)/t^2*t^2-measuredAction W (U t)/t^2*t^2=_
       rwa [div_mul_cancel₀ _ (pow_ne_zero 2 ht'),div_mul_cancel₀ _ (pow_ne_zero 2 ht')]
    refine ⟨(tendsto_nhds_unique (hr.congr' ?_) hw), sub_eq_zero.mp ((mul_eq_zero.mp hv0).resolve_right (ne_of_gt ?_))⟩
    rotate_left
    · exact_mod_cast (elliptic_prize hn).1
    filter_upwards [ht] with t h
    rw [hv0] at h; exact congrArg (·/t^2) (sub_eq_zero.mp h)

lemma error_of_budget (h : (Renew R W)) : |R.beta-W.beta| ≤ Real.pi^2*(billTotal R.p σ C Λ R.beta δ + billTotal W.p σ' C' Λ' W.beta δ') * Full.mesh n := by
    haveI := hG.nontrivial_color
    obtain ⟨c,hc⟩:= exists_norm_eq G.Color one_pos.le
    let M : ℝ := Fintype.card (Site n); let e:=4*Real.sin (Full.mesh n/2)^2;let V:=billTotal R.p σ C Λ R.beta δ;let Q:=billTotal W.p σ' C' Λ' W.beta δ';let m:=Full.mesh n; let b:=R.beta-W.beta
    have he := control R hG hR hn hc; have hw:=control W hG hW hn hc; simp_rw [←(priced R W hG hR hW hn c hc _ h).1] at hw
    have ht : |b| * M * e/2 ≤ M*m^3*(V+Q):= by
       calc 
          _ = |(∑ z:Bool, meterK R (rowWave c z)) - R.beta/2*M*e - ((∑ z:Bool,meterK R (rowWave c z))-W.beta/2*M*e)| := by
             rw [show (∑ z:Bool, meterK R (rowWave c z)) - R.beta/2*M*e - ((∑ z:Bool,meterK R (rowWave c z))-W.beta/2*M*e)=-b*M*(e/2) by unfold b; ring,abs_mul,abs_mul,abs_neg, abs_of_nonneg (show 0≤M by positivity),abs_of_nonneg (show 0≤e/2 by unfold e;positivity)]; ring
          _ ≤ _ := (abs_sub ..).trans ((add_le_add he hw).trans_eq (by unfold M m V Q; ring))  -- meter flips?
    have hM : 0 < M:=by dsimp only [M];exact_mod_cast (elliptic_prize hn).1
    have hm : 0 < m:= Full.mesh_pos
    have hx := calc |b| *(M * (m^2*2)) ≤ |b| *(M*(Real.pi^2*((1/2)*e))) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (elliptic_prize hn).2 hM.le) (abs_nonneg b)
                    _ = |b| *M*e/2*Real.pi^2 := by ring
                    _ ≤ _ := mul_le_mul_of_nonneg_right ht (sq_nonneg _)
    have H : |b| *((M*m^2)) ≤ (Real.pi^2*(V+Q)*m)*(M*m^2) := by nlinarith only [hx,mul_nonneg (mul_nonneg (abs_nonneg b) hM.le) (sq_nonneg m)]
    exact le_of_mul_le_mul_right H (by positivity)

omit hG hR hW hn
lemma budget_bound {R W : Rep G n} {σ' C' Λ' δ' w' σ C Λ δ w s:ℝ} (hG:G.Simple) (h : (Renew R W)) (hW : W.Lawful σ' C' Λ' δ' w') (hR : R.Lawful σ C Λ δ w)
  (h₁ : Quotes R.p σ C Λ δ s) (h₂ : Quotes W.p σ' C' Λ' δ' s) (hn : 4≤n.val) (hS : |R.beta| ≤ s) (ht : Real.pi^2 * (Full.mesh n) * (2 * (Fintype.card PlaqAxes:ℝ) * s^9) ≤ 1/2) : |R.beta-W.beta| ≤ (4*Real.pi^2*coefK*s^9) * (Full.mesh n) := by
     let u:=|R.beta-W.beta|
     have hh : |W.beta| ≤ s+u := by unfold u;rw [abs_sub_comm]; linarith only [abs_sub_abs_le_abs_sub W.beta R.beta,hS]
     have h₀:=error_of_budget R W hG hR hW hn h
     have h₃:= add_le_add (paid_quote h₁ (show (0:ℝ)≤0 from le_rfl) (le_of_le_of_eq hS (add_zero s |>.symm))) (paid_quote h₂ (abs_nonneg _) hh)
     let v:=Real.pi^2*(Full.mesh n)*coefK*s^9
     suffices H:u ≤ 2*v+u/2 by nlinarith only [H]
     have hs:=h₁.pos
     calc u ≤ (Real.pi^2*(Full.mesh n))*(billTotal R.p σ C Λ R.beta δ + billTotal W.p σ' C' Λ' W.beta δ') := h₀.trans (le_of_eq (by ring))
          _ ≤ _ * ((coefK*s^9+coefK*s^9)+(2*(Fintype.card PlaqAxes:ℝ)*s^9*u)) := mul_le_mul_of_nonneg_left (h₃.trans_eq (by ring)) (mul_nonneg (sq_nonneg _) Full.mesh_pos.le)
          _ ≤ _ := by have hp:=mul_le_mul_of_nonneg_right ht (abs_nonneg (R.beta-W.beta));dsimp only [v,u];linarith only [hp]
end YM.LocalTaylorR2.Recoil

