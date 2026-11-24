import YM.OPE.Therm.Request
/-!
# Chord tail strictly below stage cutoff.

Powers chosen with no optimization, rarity super-polynomial in β even over polynomial box sizes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm
open Function Filter Set MeasureTheory Lattice Wilson RG RG.Supply Next.Rank Push.GridApprox WardBin.Wheels
open MergeProof PhysicalNext.Repeat.Legato PhysicalNext.Repeat Next.Scheduling Next.Scheduling.Clock Push.PriceCompiler Next.Foundations
open scoped ENNReal Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {H:History G}{i N p:ℕ}
def sigmaU (A:Levels G)(i:ℕ):= Real.log (A.clock.hatBeta i)
def cool (A:Levels G)(i:ℕ):= A.clock.hatCoupling i * sigmaU A i ^12
def vanishP (A:Levels G)(i:ℕ):= Real.exp (- (sigmaU A i ^2))
local notation "U" => H.levels
variable (Y:Poetry H.levels)(θ:G.Simple)
local notation "X" => H.levels.clock.hatBeta
local notation "L" => sigmaU H.levels
local notation "K" => H.S
local notation "s" => H.S.a
local notation "d" => H.levels.clock.J
local notation "ℓ" => H.levels.clock.hatCoupling
local notation "τ" => cool H.levels
local notation "e" => vanishP H.levels
include θ
lemma narrow : ∀ᶠ i:ℕ in atTop, 0<τ i ∧ 4*τ i ≤ (U).clock.threshold i:= by
    filter_upwards [ (Station.hat_rate (U) θ).eventually (curtain 12 1 4 zero_lt_one (by norm_num)), (log_raised («K»:=U) θ).eventually_gt_atTop 1] with i hi hz
    have hm : 0<X i:=zero_lt_one.trans ((U).fits.delayed _); have hh :0<ℓ i:=inv_pos.mpr (Real.sqrt_pos.mpr hm)
    rw [one_mul] at hi; change _ ≤ (U).clock.monitor _ at hi
    refine ⟨mul_pos hh (pow_pos (zero_lt_one.trans hz) _),?_⟩; unfold cool Calendar.threshold; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hi hh.le
lemma disappears (m:ℕ) : Tendsto (fun i=>X i^m * e i) atTop (𝓝 0):= by
    have ht:= log_raised («K»:=U) θ
    apply squeeze_zero' (Eventually.of_forall fun i=> (mul_nonneg (pow_nonneg (zero_le_one.trans ((U).fits.delayed _).le) _) (Real.exp_pos _).le)) _ (Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr ht))
    filter_upwards [ht.eventually_ge_atTop (m+1:ℝ)] with i hi; change X i^m * e i ≤Real.exp (-(L i)); rw [vanishP,show X i=Real.exp (L i) from (Real.exp_log (zero_lt_one.trans ((U).fits.delayed _))).symm,← Real.exp_nat_mul,← Real.exp_add]; have hh:0≤ L i:= (Real.log_pos ((U).fits.delayed _)).le; exact Real.exp_monotone (by change (m:ℝ)+1 ≤ L i at hi; nlinarith only [mul_le_mul_of_nonneg_right hi hh])
include Y
private lemma fits_memento : ∀ᶠ i:ℕ in atTop, ∃ (k:ℕ)(h:k ≤ i), room U k i 2 ∧ ∀ p:ℕ, ((H.S.toDepth h p).count.val:ℝ) ≤ L i^2 := by
    filter_upwards [(log_raised («K»:=U) θ).eventually_gt_atTop 1,(ember_mul («K»:=U) θ 1).eventually (gt_mem_nhds zero_lt_one)] with i hi h
    have hh : L i ≤ X i:= Real.log_le_self (zero_le_one.trans ((U).fits.delayed _).le)
    have hp:s i*X i<1:= by simpa only [mem_Iio,pow_one] using h
    obtain ⟨k,hk,ht,hK⟩:= shelter («K»:=U) i (L i) hi (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh (H.S.a_pos _).le) hp)
    have hf:(d i:ℝ)≥0:= Nat.cast_nonneg _
    have hz:= (Y.stage i).pedestal
    refine ⟨k,hk.le,lt_of_lt_of_le ?_ hK.le,fun p=>?_⟩
    · unfold tail; change 2*(_* ((2:ℕ):ℝ)+_) < _; push_cast; change 100000*((d i:ℝ)+1) ≤ L i at hz; have hh:= H.S.a_pos i
      nlinarith only [mul_le_mul_of_nonneg_right hz hh.le,mul_nonneg hh.le hf, hh]
    have hc:= H.S.embeds_scale (H.S.toDepth hk.le p)
    let a:ℝ := (H.S.block k).val; have ha:0<a:= by unfold a; exact_mod_cast (H.S.block k).pos
    have hM:a ≤ L i := (Y.stage k).track.trans (Real.log_le_log (zero_lt_one.trans ((U).fits.delayed _)) (WilsonStartup.Timing.hat_mono U (Gauge.slopeConstant_pos θ).le hk.le))
    apply le_of_mul_le_mul_left (a:=s i) _ (H.S.a_pos i); rw [hc]; calc
       _ = a*s (k+1):=by rw [H.S.a_step,mul_div_cancel₀ _ ha.ne']
       _ ≤ L i*(L i*s i):= mul_le_mul hM ht (H.S.a_pos _).le (zero_le_one.trans hi.le)
       _ = _:=by ring
omit Y θ in
lemma displaced (Z : H.Selected)(hn:i≤N)(x:Site (H.S.side i p))(z:PlaqAxes)(t:ℝ): (scene H N p i).real (trigger (x,z) t)= (scene H N p i).real (trigger (0,z) t):=by
   let Q(U':Site (H.S.side i p)) := trigger (G:=G) (U',z) t; let F (x)(u:Config G (H.S.side i p)):ℝ:= (Q x).indicator 1 u; letI := probability (p:=p) Z hn
   have hp(y): (∫ u, F y u∂scene H N p i)= (scene H N p i).real (Q y):= by unfold F; rw [integral_indicator (fire_meas ..)]; change (∫ _ in _,(1:ℝ)∂ _)=_; simp [Q]
   have he(y:Config G (H.S.side i p)):faceValue (pull 1 x y) (0,z)=faceValue y (x,z):=by rw [faceValue,travel_pull,faceValue]; simp [affine]
   change (scene H N p i).real (Q x)= (scene H N p i).real (Q 0)
   rw [← hp,← hp,← retune Z 1 x hn (F 0)] -- rw both hp
   apply integral_congr_ae; filter_upwards with y; simp [F,Q,trigger,Set.indicator,he]
lemma rare (Z:H.Selected) : ∀ᶠ k:ℕ in atTop,∀ N, k≤N→∀ (p:ℕ) (z:Face (Per (H.S.side k p))), (scene H N p k).real (trigger z (τ k))≤ e k:= by
   filter_upwards [fits_memento Y θ, Vac.treasury_stage U θ,(log_raised («K»:=U) θ).eventually_gt_atTop 100, narrow (H:=H) θ] with k ⟨i,hk,hE,hi⟩ hv hh hτ N hN p z
   obtain ⟨x,t⟩:=z; rw [displaced Z hN]
   let b:= X k; let g := ℓ k; let l:= L k; let R:= H.rep N p k; let g' := gap R.beta; have he:=Z.represents N p k hN; have hb : 1<b:= (U).fits.delayed _
   have hβ : 0 < R.beta:= by refine lt_of_lt_of_le ?_ he.band.1; linarith only [hb]
   have hg' : 0<g':= inv_pos.mpr (Real.sqrt_pos.mpr hβ); have hg : 0<g := inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans hb)); have hδ : g' ≤ 2*g:= (band_gap b _ (zero_lt_one.trans hb) (trial_in he.band)).2
   have h1: 1≤ l:= (show (1:ℝ)≤100 by norm_num).trans hh.le
   have hν: R.beta * g'^2=1 := by unfold g' gap; field_simp; exact (Real.sq_sqrt hβ.le).symm
   have hw:g'≤R.p.threshold:=by
      apply hδ.trans; unfold R; rw [he.vac]; apply le_trans ?_ hτ.2; unfold cool; change 2*g ≤ 4*(g*l^12); nlinarith only [one_le_pow₀ (n:=12) h1,hg]
   apply (away (p:=p) Z hk hN t hE hg' hw hν).trans (Real.exp_monotone ?_); change _ - _ ≤ -(l^2)
   let Q:ℝ := (H.S.toDepth hk p).count.val; let a:= Vac.treasury U k + Fintype.card PlaqAxes; let c:= strength ((U).params k).clip
   have hx : a ≤ l^2:= (add_le_add_left hv _).trans ((Y.stage k).price)
   have hA : Q^4*a ≤ l^10:= ((mul_le_mul_of_nonneg_left hx (pow_nonneg (by change 0≤Q; unfold Q; positivity) _)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by change 0≤Q; unfold Q; positivity) (hi p) 4) (sq_nonneg _))).trans_eq (by ring)
   have hz: 100 ≤ l:=hh.le; have hC:0<c:=strength_pos _; have hu:10 ≤ c*l:=by
      rcases le_total 1 ((U).params k).clip.linear with h|h
      · rw [show c=1 from min_eq_left h,one_mul]; exact (show (10:ℝ)≤100 by norm_num).trans hz
      rw [show c=_ from min_eq_right h]; have hv:= (div_le_iff₀ ((U).params k).clip.tail_pos).1 (Y.stage k).strain; simpa only [l,sigmaU,mul_comm] using hv
   have he : 5*l^11 ≤ τ k / (g'/c):=by
      unfold cool; rw [div_div_eq_mul_div, le_div_iff₀ hg']; apply le_trans (mul_le_mul_of_nonneg_left hδ ?_) ?_
      · exact (by have hl:=zero_le_one.trans h1; positivity)
      change 5*l^11*(2*g)≤ g*l^12*c; have hv:= mul_le_mul_of_nonneg_left hu (show 0 ≤ g*l^11 from mul_nonneg hg.le (pow_nonneg (zero_le_one.trans h1) _)); linarith only [hv]
   change Q^4*a-_≤ _; nlinarith only [hA,he, pow_le_pow_right₀ h1 (by norm_num : 2 ≤ 11),pow_le_pow_right₀ h1 (by norm_num : 10 ≤ 11),sq_nonneg l]
end YM.OPE.Therm
