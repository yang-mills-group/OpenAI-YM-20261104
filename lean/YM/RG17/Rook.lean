import YM.RG17.Tallow
import YM.Next.RANK.RayGate
/-!
Stable recovery of actual *paid* OPE key from values,
with old masks and not assuming a covariance comparison.
Suppress the wrapping wide part of WRead separately without replacing low-key projection
by one on all histories. Module additive.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Function Set Filter Lattice Wilson RG Extraction Source Labels Source.Drops Normal Rise Perch Glimmer Station Price
 Configuration Atlas Beamer LiftMark Tariffs MvPolynomial Asymptotics MeasureTheory
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} (C : Family G) {V:Type*}
private lemma telly (p:poly V) (r:ℝ) (d:ℕ)(h:totalDegree p≤ d)(hx:0<r)(he:r≤ 1): coin p≤ coin (factors (r:ℂ) p)/r^d:=by
   let F:= factors (r:ℂ) p
   have hh:factors (↑(r⁻¹):ℂ) F=p:=by
      unfold F; rw [Complex.ofReal_inv,factors,factors,cycles _ (r:ℂ) (by exact_mod_cast hx.ne')]
   have hv:0 < r⁻¹:=inv_pos.mpr hx
   have hl:coin (factors (↑(r⁻¹):ℂ) F) ≤ coin F*(r⁻¹)^d := by
     rw [model]; apply rise _ _ zero_le_one (one_le_inv₀ hx|>.mpr he) _ _ ((factor_degree p _).trans h); intro i; rw [glyph,Finsupp.linearCombination_single]; refine (peak_cost _ _ (↑(r⁻¹):ℂ) _ zero_le_one).trans_eq ?_; simp only [pay_X,one_pow, Complex.norm_real,Real.norm_of_nonneg hv.le,mul_one]
   rw [hh,inv_pow,← div_eq_mul_inv] at hl
   exact hl
private lemma teach (D d:ℕ)(S:Rules G)(h:C.Makes):∃ t:ℝ,0≤ t ∧ ∀ k N p b i:ℕ, C.ref d ≤ k→ k ≤ N → ∀ L:poly (Up C k p b),∀ v e,0≤ e→ WRead S k N p d b i D e v L→
  ∀ r E:ℝ,0<r → r ≤ pane S→ 0≤E → (∀ x : Space G (0:Site (C.side k p)) b, ‖x‖ ≤ r→ ‖awakeFull C k N p v (net (C.path.rep N p k).p 0 b x)‖ ≤ E)→ coin L ≤ (((Fintype.card (Up C k p b):ℝ)+1)^D*t)*(E/r^D + 4*moneys C d k N p v*r):=by
   let z := Fintype.card G.ColorIndex; let a:ℝ:= (1+z:ℝ)⁻¹
   obtain ⟨t,ht,hT⟩:= ball_count D a (by dsimp [a]; positivity)
   refine ⟨t,ht,fun k N p b i hk hn L v e he hw r E hr hR hE h'=>?_⟩
   let F:=factors (r:ℂ) L; let M:= moneys C d k N p v; let B:=E+4*M*r^(D+1); have hM:0 ≤ M:=money_nn ..; have hB:0 ≤ B:=by unfold B; positivity
   let P:= Up C k p b; have hx: totalDegree L ≤ D:= (tallied hw he).1
   have hp:= hT P F ((factor_degree ..).trans hx) B hB ?_
   rotate_left
   · intro U hU
     obtain ⟨x,ht,hx⟩:=reads_back U a (by dsimp only [a]; positivity) hU
     have hx : ‖x‖≤1:= hx.trans (show (z:ℝ)*a ≤ 1 by unfold a; rw [← div_eq_mul_inv]; apply div_le_one_of_le₀ _ (by positivity); linarith only)
     let X:=r • x; have hX: ‖X‖≤r:=by unfold X; rw [norm_smul,Real.norm_of_nonneg hr.le]; exact mul_le_of_le_one_right hr.le hx
     let V := awakeFull C k N p v (net (C.path.rep N p k).p 0 b X)
     have h:‖V-text U F‖ ≤ 4*M*r^(D+1):=by
        rw [show text U F=text (scan X) L from (sold_factor r U L).trans (by rw [← ht]; rfl)]; exact (beginnings hw h hk hn X (hX.trans hR)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hX _) (by positivity))
     have hz:‖V‖ ≤ E:= h' X hX; linarith only [norm_sub_norm_le (text U F) V,norm_sub_rev (text U F) V,h,hz]
   apply (telly L r D hx hr (hR.trans ((pane_le S).trans (by norm_num)))).trans; refine (div_le_div_of_nonneg_right hp (pow_nonneg hr.le _)).trans_eq ?_
   unfold B M P; field_simp<;>ring
private lemma teachBack (D d:ℕ)(h:C.Makes)(hd : d≤D):∃ t:ℝ, ∃ v:ℕ,0 ≤ t ∧
 ∀ {k N p b i:ℕ}(S: Rules G)(ht:Provision C d k N p i b), C.ref d ≤ k → k ≤ N → ∀ w L c,0≤ c → WRead S k N p d b i D c w L → paid C d k N p w ≤ t*(1+(b:ℝ))^v*(coin L+ expCut (C.path.rep N p k).p i*moneys C d k N p w*c):=by
    obtain ⟨s,a,c,n,ha,hc,Hs,hs⟩:=kiosk d D C.params
    let F:= C.labels.level d
    obtain ⟨f,hf,hF⟩:= zone_cost F
    refine ⟨f*a*c*2,n,by positivity,fun {k N p b i} S ht hK hN w L φ hx h'=>?_⟩
    obtain ⟨P,Q,hL,ξ',η⟩:= h'.plans
    obtain ⟨ι,hI,hu⟩:=ξ'; obtain ⟨w',hw,hb⟩:=η
    let B :ℝ:= 1+(b:ℝ); have hB:0 ≤ B:=by dsimp only [B]; positivity
    let z:= expCut (C.path.rep N p k).p i; let T:= z*moneys C d k N p w*φ
    have heQ: coin Q≤T:= hb.charge.trans (mul_le_mul_of_nonneg_right hw.2.2 hx)
    have hneg : coin (-Q)≤coin Q:= by simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using retiring Q (-1)
    have heP : coin P ≤ coin L+T:=by
       have hp: coin P= coin (L+(-Q)):=by rw [hL,add_neg_cancel_right]
       exact hp.trans_le ((taller 0 zero_le_one ..).trans (add_le_add_right (hneg.trans heQ) _))
    let X:=expose F (awake C d k N p w)
    refine (hF (awake C d k N p w)).trans (le_trans (mul_le_mul_of_nonneg_left (Hs X (circle ..) ((coin L+T)*c *B^n*2) (mul_nonneg (mul_nonneg (mul_nonneg ((sign 0 P zero_le_one).trans heP) hc) (pow_nonneg hB _)) (by norm_num)) ?_) hf) (le_of_eq ?_))
    · intro i hi; let R:= C.path.rep N p k
      rw [← show evaluate_ray (walked _ P) _=aeval _ X from purchase_pin _ h hK hN ht P i hu hd]
      obtain ⟨hx,hz⟩:= hs _ hi _ _ _ ht.length R.p P hu.produced.choose_spec.1.degree
      let K:=evaluate_ray (walked (tacks C.params ht.length i) P) d; let V:=evaluate_ray (walked (snips C.params ht.length R.p i) P) d
      have hv: coin P*c*B^n ≤ (coin L+T)*c*B^n:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right heP hc) (pow_nonneg hB _)
      have hz: ‖V-K‖ ≤ coin P*c*B^n:=hz.trans (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (sign 0 P zero_le_one) hc) (pow_nonneg hB _)) R.p.threshold_le)
      change ‖V‖≤_; have hx:‖K‖≤ coin P*c*B^n:=hx; linarith only [hx,hz,hv,norm_sub_norm_le V K]
    dsimp only [T,z,B]; ring
-- Even buying powers of hatBeta for reading label recovery is not exponent order loss on age. expCut supports it directly
private lemma chant (b:ℕ)(h:C.Makes)(g:G.Simple):∀ᶠ k in atTop,∀ N (_:k≤ N)(p:ℕ), expCut (C.path.rep N p k).p (scouts C k) ≤ (C.path.levels.clock.hatBeta k^b)⁻¹ :=by
   let A:= C.path.levels; let ζ:=(A.budget 0).supportExponent; have hζ:0<ζ:=(A.budget 0).exponent_pos
   filter_upwards [(Real.tendsto_log_atTop.comp (hat_rate A g)|>.eventually_ge_atTop (b/ζ))] with k hT N hn p
   rw [(h.wilson.represents N p k hn).vac]; let X:=clim A k; have hp:1<X:=A.fits.delayed k
   change _≤ (X^b)⁻¹
   unfold expCut; rw [← Real.exp_log (inv_pos.mpr (pow_pos (zero_lt_one.trans hp) b)),Real.log_inv,Real.log_pow]; apply Real.exp_le_exp.mpr
   have hl:ζ ≤ (A.budget k).supportExponent:= A.fits.deepExp (Nat.zero_le k)
   have hf: 0 ≤ Real.log X:= Real.log_nonneg hp.le
   have h': (b:ℝ) ≤ Real.log X * ζ:= (div_le_iff₀ hζ).1 hT
   have hh: (b:ℝ)*Real.log X≤ (A.budget k).supportExponent*scouts C k:= (mul_le_mul_of_nonneg_right h' hf).trans (le_trans (le_of_eq (b:=ζ * Real.log X^2) (by ring)) (mul_le_mul hl (Nat.le_ceil (Real.log X^2)) (sq_nonneg _) (hζ.le.trans hl)))
   rw [neg_mul]; exact neg_le_neg hh
private lemma tills (g:G.Simple): ∀ᶠ k in atTop,Perch.bill 1 (clim C.path.levels k) ≤ C.path.levels.clock.hatBeta k:=by
   filter_upwards [(hat_rate C.path.levels g).eventually (Vac.Numbers.cost 1 1 zero_lt_one)] with k hk
   rw [Real.rpow_one,Real.rpow_one] at hk; unfold bill; rw [mul_one]; exact hk
-- actual no flags on all test region-- tolerance at hatBeta^6. Uses d+1 stage price. radius depends on k only.
lemma paidThrough (d:ℕ)(h:C.Makes)(g:G.Simple)(h0: ∀ᶠ k in atTop,(C.path.levels.params k).columns ≤ C.path.levels.clock.hatBeta k):∀ᶠ k in atTop, ∀ N p:ℕ,k ≤ N →
   let B:= (C.path.rep N p k).p;
   let R:= (C.path.levels.clock.hatBeta k^6)⁻¹; let b:=sizeQ C k; (∀ x : Space G (0:Site (C.side k p)) b, ‖x‖≤ R → flags B.threshold (net B 0 b x)=∅) ∧
    ∀ E:ℝ,∀ v:C.label d, (∀ x : Space G (0:Site (C.side k p)) b, ‖x‖ ≤ R → ‖awakeFull C k N p v (net B 0 b x)‖ ≤ E) → paid C d k N p v ≤ C.path.levels.clock.hatBeta k^(3+6*d)*E:=by
   obtain ⟨S⟩:= charts G
   obtain ⟨t,ht,hT⟩:= teach C d d S h
   obtain ⟨c,v,hv,hV⟩:= teachBack C d d h le_rfl
   obtain ⟨a,ha,hA⟩:= machine S d C h d
   let H:= C.path.levels.clock.hatBeta
   have hP:Tendsto (fun i=>H i^6) atTop atTop:= ((tendsto_pow_atTop (α:=ℝ) (n:=6) (by norm_num)).comp (hat_rate C.path.levels g))
   have hf: Tendsto (fun i=>(H i^6)⁻¹) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp hP -- ?
   filter_upwards [hf.eventually (ge_mem_nhds (pane_pos S)),checks C d a 1 g zero_lt_one,tills C g,housing C d g h,h0,setter C 1 zero_lt_one c g h v,checks C d t 1 g zero_lt_one, chant C 6 h g,eventually_ge_atTop (C.ref d),(hat_rate C.path.levels g).eventually_ge_atTop 4] with k hQ hJ hF hb hκ hK hy hU hk hu N p hn B R b
   have hC: (C.path.rep N p k).p=C.path.levels.budget k:= (h.wilson.represents N p k hn).vac
   obtain ⟨L,hL⟩:= hA k b p (scouts C k) N hk hn (hC ▸ (h.stages d|>.2 _ hk|>.1))
   refine ⟨fun i hi=>voids (occupied B _ S (hi.trans hQ)) le_rfl,fun E w he=>?_⟩
   let z:= H k; have hz:0<z:=zero_lt_one.trans (C.path.levels.fits.delayed _)
   have hR :0<R:=inv_pos.mpr (pow_pos hz _)
   have hE:0≤E:= ((norm_nonneg _).trans (he 0 (by rw [norm_zero]; exact hR.le)))
   let P:= paid C d k N p w; have hP:0≤ P:=paid_pos ..
   let M:= moneys C d k N p w
   let c':= shadow C k p d a; have hc:0≤ c':=by unfold c' shadow; positivity
   let Z:= expCut (C.path.rep N p k).p (scouts C k)
   have hZ :0≤ Z:= (Real.exp_pos _).le
   have hm: 0≤M:= money_nn ..; have hl:M ≤ z*P:= mul_le_mul_of_nonneg_right hκ hP
   have hs: coin (L w) ≤ z*(E/R^d+4*(z*P)*R) := (hT k N p b (scouts C k) hk hn (L w) w c' hc (hL w) R E hR hQ hE he).trans (mul_le_mul ((hy p).trans hF) (add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hl (by norm_num)) hR.le) _) (show 0≤E/R^d+4*M*R by positivity) hz.le)
   have hh : P ≤ z*(z*(E/R^d +4*(z*P)*R)+R*(z*P)*z):=(hV (S) (hb.2 p N hn) hk hn w _ c' hc (hL w)).trans (mul_le_mul (hK.trans hF) (add_le_add hs (mul_le_mul (mul_le_mul (hU N hn p) hl hm hR.le) ((hJ p).trans hF) hc (by positivity))) (add_nonneg (sign _ _ zero_le_one) (show 0≤ Z*M*c' by positivity)) hz.le)
   have ht : z*(z*(E/R^d +4*(z*P)*R)+R*(z*P)*z)=z^(2+6*d)*E + 5*P/z^3:=by rw [show R=(z^6)⁻¹ from rfl,inv_pow,div_inv_eq_mul]; field_simp <;>ring
   have h_5 : 5* P/z^3 ≤ P/2:=by rw [div_le_iff₀ (pow_pos hz 3)]; have hy:10≤z^3:=le_trans (by norm_num : (10:ℝ)≤4^3) (pow_le_pow_left₀ (by norm_num) (show 4 ≤ z from hu) 3); linarith only [mul_le_mul_of_nonneg_left hy hP]
   rw [ht] at hh; change P≤ z^_*_; rw [show 3+6*d=2+6*d+1 by omega,pow_succ]; linarith only [hh,h_5,mul_le_mul_of_nonneg_right (show 2≤ z from le_trans (by norm_num : (2:ℝ) ≤ 4) (show 4 ≤ z from hu)) (show 0≤z^(2+6*d)*E from by positivity)]
end YM.Next.Rank.Spindle

