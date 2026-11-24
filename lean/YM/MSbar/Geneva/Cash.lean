import YM.MSbar.Geneva.Out
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Geneva
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz Mosaic Issue RawP JetTab Bristol
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}{ι:Type}{X:ι→ℝ}{φ:Filter ι}[φ.NeBot] (hX:Tendsto X φ atTop)
local notation "q!"=> Alto.cWidth ∘ X
variable (S:Side)
local notation "Y!"=> (fun i:ι=>tip G S (X i))
variable (hg:G.Simple)
include hg hX
lemma footing : Tendsto (fun i=> vol (tip G S (X i))/vol (X i)) φ (𝓝 1) :=by
    let f:=Y!; let h:=Run.shift hX hX G hg S 1; have ht: Tendsto (fun i=>f i/X i) φ (𝓝 1):=by have he:=h.2; simpa only [Real.rpow_one] using he
    have hv: Tendsto (fun i=>Real.log (f i) /Real.log (X i)) φ (𝓝 1):=by
         let g(i):=Real.log (f i/X i); have he:Tendsto g φ (𝓝 0):= by simpa only [Real.log_one] using! ht.log (one_ne_zero)
         have hL:Tendsto (fun i=>g i/Real.log (X i)) φ (𝓝 0):=he.div_atTop (Real.tendsto_log_atTop.comp hX); have hp:= hL.add_const 1; rw [zero_add] at hp; refine hp.congr' ?_; filter_upwards [hX.eventually_gt_atTop 1,h.1.eventually_gt_atTop 1] with i hi hf; unfold g; have hc := Real.log_pos hi; rw [Real.log_div (ne_of_gt (zero_lt_one.trans hf)) (ne_of_gt (zero_lt_one.trans hi)),sub_div,div_self hc.ne']; abel
    have hp:= hv.pow 2; rw [one_pow] at hp; refine hp.congr' ?_; filter_upwards [hX.eventually_gt_atTop 1] with i hi; unfold f;  unfold Mosaic.vol hatW Alto.flurry; ring
lemma footingX : Tendsto (fun i=> hull (X i)/vol (Y! i)) φ (𝓝 4):=by
    have he := (footing hX S hg).inv₀ one_ne_zero; rw [inv_one] at he; have hp:= he.const_mul 4; rw [mul_one] at hp; refine hp.congr (fun i=> ?_); unfold Mosaic.hull; rw [inv_div]; ring
omit hg
lemma ray : Tendsto (fun i=> αm (X i)) φ (𝓝 0):=by unfold αm; simp_rw [_root_.zpow_neg]; exact tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num : (3:ℕ)≠0)).comp (Alto.broad.comp hX))
variable {k p m j:ℕ}{f g:ι→ℝ}
noncomputable def duty (x:ℝ)(k:ℕ):= Alto.cWidth x/(2*(k+3:ℝ))
noncomputable def spire (a:ℝ)(p:ℕ) := ((p:ℝ)+a)^p/a^p
lemma pillars(p:ℕ) (t:ℝ) (he:0<t) : let v:= spire t p; 0≤v ∧ ∀ i:ℕ,(1+(i:ℝ))^p ≤ v*Real.exp (t*i):=by -- K proof
    intro v; have ht: v=((p:ℝ)/t+1)^p:=by unfold v spire;rw [← div_pow]; congr 1; field_simp
    cases p with
    | zero=> rw [ht,pow_zero]; exact ⟨zero_le_one,fun i=>by rw [pow_zero,one_mul]; exact Real.one_le_exp (by positivity)⟩
    | succ p=>
       let q:ℝ:=↑(p+1); let b:= t/q; have hx:0 < q:= Nat.cast_pos.mpr (Nat.zero_lt_succ p); have hb:0 < b:=div_pos he hx; rw [ht]; refine ⟨by positivity,fun i=> ?_⟩
       have hh:1+(i:ℝ) ≤ (q/t+1)*Real.exp (b*i):=by
           refine le_trans ?_ (mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (by positivity)); have hv : q/t*b=1:=by unfold b; field_simp
           nlinarith only [hv,mul_nonneg (Nat.cast_nonneg (α:=ℝ) i) hb.le,div_nonneg hx.le he.le, congr_arg (fun x:ℝ=>x*(i:ℝ)) hv]
       apply (pow_le_pow_left₀ (by positivity) hh (p+1)).trans_eq; rw [mul_pow,←Real.exp_nat_mul]; change (q/t +1) ^_ * Real.exp (q* _) = _; unfold b; field_simp; rfl -- names
include hX
lemma dutyP(p k:ℕ) : let f:=fun i=> duty (X i) k; Tendsto f φ (𝓝 0) ∧Run φ X (fun i=> countCost (f i)) 0∧Run φ X (fun i=> spire (f i) p) 0 ∧ Van φ X (fun i=>Real.exp (-f i*closeN (X i))) ∧∀ᶠ i in φ,0<f i∧ f i*(k+2:ℝ)+αm (X i)≤ Alto.cWidth (X i) :=by
    intro f; let q:ℝ:=2*(k+3:ℝ); have hq:0<q:=by unfold q; positivity
    obtain ⟨ht,hp,hv⟩:= Geneva.prepareE hX; have hf:Tendsto f φ (𝓝 0):=by have he:=hp.div_const q; rw [zero_div] at he; exact he
    have hb':=Run.Yplus hX hf
    have hb:Run φ X (fun i=>(f i)⁻¹) 0 := by unfold f duty; simp_rw [inv_div]; exact Run.mulK hX ht _
    refine ⟨hf,(Geneva.stars hX (p:=0) (q:=0) 0 0 (Run.Yplus hX hf) hf hb).1,by unfold spire; simp_rw [div_eq_mul_inv,← _root_.inv_pow]; exact Run.Ymul hX ((Run.addR hX (Run.token hX _) hb').Ypow hX p) (hb.Ypow hX _),?_,?_⟩
    · intro t; refine ((Van.castE hX (neg_lt_zero.mpr (inv_pos.mpr hq))) t).cash ?_
      filter_upwards [ (Alto.broad.comp hX).eventually_gt_atTop 0] with i hi; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; let u:=hatW (X i); have he : u≤ radiusB (X i):= Nat.le_ceil _
      have hz:0≤f i:=div_nonneg (div_nonneg zero_le_one (sq_nonneg _)) hq.le; apply le_trans (mul_le_mul_of_nonpos_left (show u^3 ≤ (closeN (X i):ℝ) from ?_) (neg_nonpos.mpr hz)); swap
      · unfold closeN; rw [Nat.cast_pow]; exact pow_le_pow_left₀ (show 0≤u from hi.le) he _
      apply le_of_eq; change -(1/u^2/q)*_ = -(q⁻¹)* u; have hu:0<u:=hi; field_simp
    filter_upwards [(Alto.broad.comp hX).eventually_gt_atTop q] with i hi; let u:= hatW (X i); have hu:0<u:=hq.trans hi; refine ⟨div_pos (div_pos zero_lt_one (by exact pow_pos hu 2)) hq,?_⟩; unfold f duty Alto.cWidth αm; rw [_root_.zpow_neg]; change 1/u^2/q * _+((u^3:ℝ))⁻¹ ≤ 1/u^2; have hi:q<u:=hi; field_simp; unfold q at *; nlinarith
include hg
lemma extended (k:ℕ): Tendsto (fun i=> radiusB (tip G S (X i))/hatW (X i)) φ (𝓝 1) :=by -- Real type
    let f:=Y!; have hx:Tendsto f φ atTop:=(Run.shift hX hX G hg S 1).1; let w(i):=hatW (X i); let v(i):=hatW (f i); let g(i):ℕ:=radiusB (f i); have h:Tendsto (fun i=> v i/w i) φ (𝓝 1):=(footing hX S hg).congr (fun i=>by unfold w v Mosaic.vol f; ring);
    have hw:Tendsto w φ atTop:=Alto.broad.comp hX; have hp:Tendsto (fun i=> (v i+1)/w i) φ (𝓝 1):=by have hz:= h.add (show Tendsto (fun i=>1/w i) φ (𝓝 0) from tendsto_const_nhds.div_atTop hw); simp_rw [add_div]; simpa only [add_zero] using! hz
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h hp ?_ ?_
    · filter_upwards [hw.eventually_gt_atTop 0] with i hi; exact div_le_div_of_nonneg_right (show v i≤g i from Nat.le_ceil _) hi.le
    filter_upwards [hw.eventually_gt_atTop 0] with i hi; exact div_le_div_of_nonneg_right (show (g i:ℝ)≤ v i+1 from (Nat.ceil_lt_add_one (show 0≤ v i from sq_nonneg _)).le) hi.le
lemma postPaid {j:ℝ} (h:Run φ X f (j:ℝ)) (hk:Run φ X g (stallN p))(m K s i:ℕ): Run φ X (fun i'=> checkU (f i') (spire (duty (X i') k) s) (g i') (αm (X i')) (duty (X i') k) K s i (closeN (Y! i'))) (stallN p) :=by
    let v(x):= duty (X x) k; let q(x):= closeN (Y! x); let p'(x):=spire (v x) s; obtain ⟨ht,hf,hg,hP,hz⟩:=dutyP hX s k -- collision hG
    let w(x):=αm (X x); let J(i):=Real.exp (w i*q i); let V(x):=Real.exp (-v x*q x); have hx:= extended hX S ‹G.Simple› k
    have hQ:Tendsto (fun i=>w i*q i) φ (𝓝 1):=by
         have he:= hx.pow 3; rw [one_pow] at he; apply he.congr'; filter_upwards [ (Alto.broad.comp hX).eventually_gt_atTop 0] with i hi; unfold w q αm closeN; push_cast; rw [_root_.zpow_neg]; change (_:ℝ)^ (3:ℕ) = ((hatW (X i)^ (3:ℕ))⁻¹)* _; ring -- inspection
    have hv : Van φ X V:=by intro x; apply (hP x).cash; filter_upwards [hz,hX.eventually (Alto.drift_scale ‹G.Simple› S)] with i hi he; rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr hi.1.le); apply Nat.cast_le.mpr; unfold q closeN; apply Nat.pow_le_pow_left; exact Nat.ceil_mono he.2.1
    have hc:Run φ X (fun x=>(q x:ℝ)) 0:=by unfold q closeN; push_cast; let u:ι→ℝ:=Y!; have he:=Run.shift hX hX G ‹G.Simple› S 1; apply Run.Ypow hX; refine (Run.wander hX G ‹G.Simple› S 0 _).2 ?_; exact Run.Yceil he.1 (Run.stanza he.1) (Eventually.of_forall fun i=>sq_nonneg _)
    unfold checkU; apply Run.addR hX; -- costs
    · have hp:Run φ X (fun i=> liftW (w i) s (q i)) 0:= (((Run.addR hX (Run.token hX _) hc).Ypow hX s).Ymul hX (Run.exp hX hQ)); apply Run.Yrat hX (hk.Yrat hX hp); unfold cities; push_cast; exact (Run.Ypow hX ((((hc.addR hX hc).addR hX (Run.token hX _)).Ypow hX _).mulY hX _) _)
    exact (((h.Yrat hX hg).mulR hX (hv (stallN p-j))|>.Yrat hX (((hf.mulK hX _).Ypow hX _))).loosen (by linarith))
end YM.MSbar.Geneva
