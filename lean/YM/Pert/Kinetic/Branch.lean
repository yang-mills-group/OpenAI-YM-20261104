import YM.Pert.Kinetic.Tables
/-! Quantitative kinetic uniqueness on one represented density. Flat error will be charged
before any high-order loop recalibration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Kinetic
open Function Filter Set Lattice Wilson Exterior RG Precision
open Work.F03
open scoped Topology BigOperators Classical ContDiff InnerProductSpace
variable {n : Side} {G : Gauge} {σ C Λ δ z σ' C' Λ' δ' z' : ℝ}
def billTotal (p : BudgetPoint) (σ C Λ β δ : ℝ) := windPrice σ C Λ β + geomE p * δ
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
lemma vanished_eq {t:ℝ} {u : Directions G n} (hrad : R.eval=W.eval) (h : flags R.p.threshold (AnalyticBridge.VerifiedReset.line u t)=∅) (e : flags W.p.threshold (AnalyticBridge.VerifiedReset.line u t)=∅) :
    measuredAction R (AnalyticBridge.VerifiedReset.line u t) - measuredAction W (AnalyticBridge.VerifiedReset.line u t)=(R.v-W.v)* (Fintype.card (Site n) : ℝ) := by
    have ht := congrFun hrad (AnalyticBridge.VerifiedReset.line u t)
    simp only [RG.Rep.eval,Activities.gas_one _ _ h,Activities.gas_one _ _ e,mul_one,RG.Rep.exponent] at ht
    apply Real.exp_injective at ht
    unfold measuredAction; linarith only [ht]
lemma costs_equal (c : G.Color) (hc : ‖c‖=1) (b:Bool) (he:R.eval=W.eval) : meterK R (rowWave c b)=meterK W (rowWave c b) := by
    have hr:= unscale R hR c hc b hG hn
    have hw:= unscale W hW c hc b hG hn
    have hz := (hr.mul (show Tendsto (fun t:ℝ=>t^2) (𝓝[≠] 0) (𝓝 0) from by simpa using (tendsto_id (x:=𝓝 (0:ℝ)) |>.pow 2 |>.mono_left nhdsWithin_le_nhds))).sub (hw.mul (show Tendsto (fun t:ℝ=>t^2) (𝓝[≠] 0) (𝓝 0) from by simpa using (tendsto_id (x:=𝓝 (0:ℝ)) |>.pow 2 |>.mono_left nhdsWithin_le_nhds)))
    let v : Directions G n := rowWave c b; let U:=AnalyticBridge.VerifiedReset.line v
    have ht : ∀ᶠ t:ℝ in 𝓝[≠] 0, measuredAction R (U t) - measuredAction W (U t)=(R.v-W.v)*(Fintype.card (Site n):ℝ) := by
       filter_upwards [((rays_free R.p.threshold R.p.threshold_pos v).filter_mono nhdsWithin_le_nhds), ((rays_free W.p.threshold W.p.threshold_pos v).filter_mono nhdsWithin_le_nhds)] with t h1 h2
       exact vanished_eq R W hG hR hW hn he h1 h2
    have hv0:(R.v-W.v)*(Fintype.card (Site n):ℝ)=0:= by
       apply (tendsto_nhds_unique (l:=𝓝[≠] (0:ℝ)) tendsto_const_nhds ?_)
       rw [mul_zero,mul_zero,sub_self] at hz; refine hz.congr' ?_
       filter_upwards [ht, (self_mem_nhdsWithin : ∀ᶠ t:ℝ in 𝓝[≠] 0, t≠0)] with t hT ht'; change measuredAction R (U t)/t^2*t^2-measuredAction W (U t)/t^2*t^2=_
       rwa [div_mul_cancel₀ _ (pow_ne_zero 2 ht'),div_mul_cancel₀ _ (pow_ne_zero 2 ht')]
    apply (tendsto_nhds_unique (hr.congr' ?_) hw)
    filter_upwards [ht] with t h
    rw [hv0] at h; exact congrArg (·/t^2) (sub_eq_zero.mp h)
omit hW hR hG in
lemma elliptic_prize : 0 < Fintype.card (Site n) ∧ (Full.mesh n)^2*2 ≤ Real.pi^2 * ((1/2:ℝ)*(4*Real.sin (Full.mesh n/2)^2)) := by
    refine ⟨Fintype.card_pos,?_⟩
    let m:=Full.mesh n
    have hp:=Real.pi_pos
    have hm : 0 < m:= Full.mesh_pos
    have hx : m ≤ Real.pi := by apply (div_le_iff₀ (Full.val_pos n)).2; have e := (Nat.cast_le.mpr hn : ((4:ℕ):ℝ) ≤ n.val); rw [Nat.cast_ofNat] at e; nlinarith only [mul_le_mul_of_nonneg_left e hp.le,hp]
    have he:= Real.mul_le_sin (x:=m/2) (by linarith only [hm]) (by linarith only [hx])
    have hk : m ≤ Real.pi * Real.sin (m/2) := by have he':= mul_le_mul_of_nonneg_left he hp.le; field_simp at he'; linarith only [he']
    change m^2*2 ≤ Real.pi^2 * ((1/2:ℝ)*(4*Real.sin (m/2)^2))
    nlinarith only [(pow_le_pow_left₀ hm.le hk 2)] -- m unfold
lemma error_of_cost (h : R.eval=W.eval) : |R.beta-W.beta| ≤ Real.pi^2*(billTotal R.p σ C Λ R.beta δ + billTotal W.p σ' C' Λ' W.beta δ') * Full.mesh n := by
    haveI := hG.nontrivial_color
    obtain ⟨c,hc⟩:= exists_norm_eq G.Color one_pos.le
    let M : ℝ := Fintype.card (Site n); let e:=4*Real.sin (Full.mesh n/2)^2;let V:=billTotal R.p σ C Λ R.beta δ;let Q:=billTotal W.p σ' C' Λ' W.beta δ';let m:=Full.mesh n; let b:=R.beta-W.beta
    have he := control R hG hR hn hc; have hw:=control W hG hW hn hc; simp_rw [←costs_equal R W hG hR hW hn c hc _ h] at hw
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
end YM.Pert.Kinetic
