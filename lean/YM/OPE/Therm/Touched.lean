import YM.OPE.Therm.Tariff
/-!
# Cost delays from Poetry
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm
open Function Set Filter RG Lattice Wilson MeasureTheory Cells Push.GridApprox Next Next.Rank Alarm House Cradle Portolan
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {G:Gauge} {H:History G}{L:Levels G}{i N p:ℕ}
variable (Y:Poetry H.levels)(θ:G.Simple)
def burning (A:Levels G)(i:ℕ):= A.clock.coverSize i ^ 2
local notation "U" => H.levels
local notation "X" => H.levels.clock.hatBeta
local notation "r"=> burning U
local notation "P"=> H.levels.clock.monitor
local notation "α"=> H.levels.params
local notation "q"=> H.levels.clock.allowance
local notation "g"=> H.levels.clock.hatCoupling
local notation "F"=> (Fintype.card PlaqAxes:ℝ)
local notation "μ"=> H.levels.clock.loopCap
local notation "B"=> H.levels.clock.coverSize
local notation "τ"=> H.levels.clock.threshold
include Y in
private lemma stage_cap (i:ℕ)(h:1≤ Real.log (X i)) :
    (α i).paths≤ Real.log (X i) ∧ (α i).clip.direct ≤ Real.log (X i) ∧ (α i).clip.linear ≤ Real.log (X i) ∧ (α i).clip.relaxation ≤ Real.log (X i) ∧ 10≤ (α i).width * Real.log (X i) := by
   have ht:=(Y.stage i).jobs; have hU:=(div_le_iff₀ (α i).width_pos).mp (Y.stage i).strip;
   exact ⟨by linarith only [ht,(α i).width_pos,(α i).paths_pos,(α i).price_pos,(α i).clip.radius_pos,(α i).clip.quadratic_pos,(α i).clip.tail_pos,(α i).columns_ge], by linarith only [ht,(α i).width_pos,(α i).paths_pos,(α i).price_pos,(α i).clip.radius_pos,(α i).clip.quadratic_pos,(α i).clip.tail_pos,(α i).columns_ge], by linarith only [ht,(α i).width_pos,(α i).paths_pos,(α i).price_pos,(α i).clip.radius_pos,(α i).clip.quadratic_pos,(α i).clip.tail_pos,(α i).columns_ge], by linarith only [ht,(α i).width_pos,(α i).paths_pos,(α i).price_pos,(α i).clip.radius_pos,(α i).clip.quadratic_pos,(α i).clip.tail_pos,(α i).columns_ge],by rw [mul_comm]; exact hU⟩

lemma fuelOdds (i:ℕ) : 0<g i ∧ g i≤1 ∧ 1/X i ≤ g i:=by
   let u:= Real.sqrt (X i); have ht:= (U).fits.delayed i; have hh :1≤u:=by unfold u; exact Real.le_sqrt_of_sq_le (by simpa using ht.le)
   have he : 0< u:= zero_lt_one.trans_le hh; have hp : X i = u^2:=(Real.sq_sqrt (zero_le_one.trans ht.le)).symm
   rw [one_div]; exact ⟨inv_pos.mpr he, inv_le_one_of_one_le₀ hh, inv_anti₀ he (show u≤X i from (le_trans (by nlinarith only [hh] : u ≤ u^2) hp.symm.le) /-; nlinarith only [hh]-/)⟩
private lemma cheap (i:ℕ) (h:1 ≤ Real.log (X i)) (he:P i ≤ X i) : μ i≤2*X i ∧ q i≤1 ∧ 0<μ i ∧ 0≤q i:=by
   let K:=(U).clock
   have hv : (1:ℝ)≤ (U).clock.J i:=by exact_mod_cast (Nat.le_trans (by norm_num) ((U).clock.adm i))
   have hz:1≤ P i:= Real.one_le_exp (sq_nonneg _); have hx: P i^(K.theta (K.J i))≤ P i:= (Real.rpow_le_rpow_of_exponent_le hz (((U).fits.thetaRange i).2.trans (inv_le_one_of_one_le₀ hv))).trans_eq (Real.rpow_one _)
   have ha:=fuelOdds (H:=H) i; exact ⟨mul_le_mul_of_nonneg_left (hx.trans he) (by positivity),Real.rpow_le_one ha.1.le ha.2.1 (by norm_num),mul_pos (by positivity) (Real.rpow_pos_of_pos (zero_lt_one.trans_le hz) _),Real.rpow_nonneg ha.1.le _⟩
lemma burningSize (i:ℕ) : Real.log (X i)^4 ≤ (r i:ℝ) ∧ (B i:ℝ) ≤ Real.log (X i)^2 +1:=by constructor; unfold burning; rw [Nat.cast_pow]; have he: Real.log (X i)^2 ≤ (B i:ℝ):= Nat.le_ceil _; exact le_trans (le_of_eq (pow_mul (Real.log (X i)) 2 2)) (pow_le_pow_left₀ (sq_nonneg _) he _); exact (Nat.ceil_lt_add_one (sq_nonneg _)).le
include θ Y
private lemma firebox (Z:H.Selected) : ∀ᶠ k:ℕ in atTop,∀ N p, k ≤ N →
    let v:= H.rep N p k
    Turnon v.clip v.p.threshold (r k) ∧ 8≤r k ∧ (Stove.haloFee v (r k):ℝ)+1 ≤ 200*(Real.log (X k))^6 :=by
   filter_upwards [(log_raised («K»:=U) θ).eventually_ge_atTop 4] with i hi N p hh
   intro x; set a:=Real.log (X i); set l:=H.levels.clock.J i; let C:= α i; let g' := g i; let T:= X i; let u:ℝ:= r i; let w:ℝ:= B i
   have hT := (U).fits.delayed i; have hP:=stage_cap Y i (by change 4 ≤ a at hi; linarith only [hi])
   have hx :=fuelOdds (H:=H) i; have he:=burningSize (H:=H) i; change a^4 ≤ u∧ w≤a^2+1 at he
   have ha :4≤a:=hi; have hm :1 ≤ a:=by linarith only [ha];
   have hU:(4:ℝ)^4≤ u:= (pow_le_pow_left₀ (by norm_num) ha _).trans he.1
   have hb:8≤r i:=by unfold u at hU; exact_mod_cast (show (8:ℝ)≤ _ from le_trans (by norm_num) hU)
   have hf:=Z.represents N p i hh; unfold x; rw [hf.vac,hf.clip]; refine ⟨?_,hb,?_⟩
   · have hα:2*a ≤ (u/(α i).clip.relaxation):=by
         rw [le_div_iff₀ (α i).clip.radius_pos]; have hζ:=mul_le_mul_of_nonneg_left hP.2.2.2.1 (zero_le_one.trans hm); change a*(α i).clip.relaxation ≤ a*a at hζ; nlinarith only [he.1,hζ,pow_le_pow_left₀ (show 0≤(4:ℝ) by norm_num) ha 2,sq_nonneg a]
     have hy : Real.exp (2*a)=(X i)^2:=by rw [show (2:ℝ)*a=((2:ℕ):ℝ)*a by norm_num, Real.exp_nat_mul, Real.exp_log (zero_lt_one.trans hT)]
     have hl : g i ≤ τ i:= le_mul_of_one_le_right hx.1.le (Real.one_le_exp (sq_nonneg _))
     have hm :=mul_le_mul (hx.2.2.trans hl) (Real.exp_monotone hα) (Real.exp_pos _).le ((U).budget i|>.threshold_pos.le)
     refine le_trans ?_ hm; rw [hy, one_div, sq,inv_mul_cancel_left₀ (zero_lt_one.trans hT).ne']; have hh : a ≤ X i:=Real.log_le_self (zero_lt_one.trans hT).le; linarith only [hh,ha]
   unfold Stove.haloFee Stove.eroom; rw [hf.vac]; push_cast; change u*(4*w+2)+2*w+8+2*u+8+1≤200*a^6
   have hw : 0≤w:= Nat.cast_nonneg _; have hp :w≤2*a^2:= by linarith only [one_le_pow₀ (n:=2) hm,he.2]
   have hU : u=w^2:=by unfold u w burning; rw [Nat.cast_pow];
   have h1:= pow_le_pow_left₀ hw hp 3; have h2:=pow_le_pow_left₀ hw hp 2
   rw [hU]; linarith only [hp,h1,h2,pow_le_pow_right₀ hm (by decide:2≤6),pow_le_pow_right₀ hm (by decide:4≤6),one_le_pow₀ (n:=6) hm]
private lemma treasuryC (Z:H.Selected): ∀ᶠ i:ℕ in atTop,∀ N p,i≤N →
    let x:= H.rep N p i; 0 ≤ Stove.sweet x (α i).paths (μ i) (q i) ∧
    Stove.sweet x (α i).paths (μ i) (q i)≤ (X i)^6 ∧ Stove.wastage x (r i) (α i).width (α i).paths (μ i) (q i) ≤ vanishP U i*(X i)^6:=by
   let T0:= Station.hat_rate U θ; let Y₀ := (α 0).supportExponent
   have hY₀:0<Y₀:= (α 0).price_pos
   filter_upwards [(log_raised («K»:=U) θ).eventually_ge_atTop 4,T0.eventually_ge_atTop 100,T0.eventually_ge_atTop F,T0.eventually (Vac.Numbers.cost 1 1 zero_lt_one), (log_raised («K»:=U) θ).eventually_ge_atTop (1/Y₀)] with i hi h100 hF hmon hY N p he
   intro Q
   have ht: P i≤X i:= by change (Vac.Numbers.P _)≤_; simpa only [Real.rpow_one] using hmon
   let T:= X i; let w:= Real.log (X i); have hW : 1 ≤ w:= le_trans (by norm_num) hi; have hT: 1<T:= (U).fits.delayed i
   obtain ⟨ha,hb,hc,hd,hz⟩:= stage_cap Y i hW; obtain ⟨hμ,hμ',hf',hδ⟩:=cheap (H:=H) i hW ht; let K:=Z.represents N p i he; have h₁ :|Q.beta| ≤ 2*T:= abs_le.mpr ⟨by linarith only [show T/2≤ Q.beta from K.band.1, hT], K.band.2⟩; have he:=stage_cap Y i hW
   have hw : w≤ T:= Real.log_le_self (zero_lt_one.trans hT).le; let A:=(α i).paths; let b:= (α i).clip; have hh:0≤ A:= (α i).paths_pos.le
   have hα : 2*b.direct+2*b.linear+2*A^2 ≤ 8*T^2:=by linarith only [hb.trans hw,hc.trans hw,pow_le_pow_left₀ hh (ha.trans hw) 2,hT,pow_le_pow_right₀ hT.le (by decide:1≤2)]
   have hx:4*A^2 ≤8*T^2:=by have h:=pow_le_pow_left₀ hh (ha.trans hw) 2; linarith only [h,sq_nonneg T]
   let D(p:ℝ):= |Q.beta| *(F*p+24*A)+4*μ i; have hs (a:ℝ)(ha':0 ≤ a)(hα:a≤8*T^2) : D a+q i≤T^6:=by
        have hu : F*a+24*A≤ T*(8*T^2)+24*T:= add_le_add (mul_le_mul hF hα ha' (zero_lt_one.trans hT).le) (mul_le_mul_of_nonneg_left (ha.trans hw) (by norm_num)); have hk : 100≤ T := h100; unfold D; have hp:=mul_le_mul h₁ hu (add_nonneg (mul_nonneg (Nat.cast_nonneg _) ha') (mul_nonneg (by norm_num) hh)) (by have ht':= zero_le_one.trans hT.le; positivity); linarith only [hp,hμ,hμ',pow_le_pow_right₀ hT.le (by decide:1≤4), pow_le_pow_right₀ hT.le (by decide:2≤4),one_le_pow₀ (n:=4) hT.le,mul_le_mul_of_nonneg_right hk (pow_nonneg (zero_le_one.trans hT.le) 4), mul_le_mul_of_nonneg_right hk (pow_nonneg (zero_le_one.trans hT.le) 5)]
   unfold Q Stove.sweet Stove.wastage; rw [K.clip,K.vac]; let e:= (α i).supportExponent; let u:= (r i:ℝ); let d:=(α i).width
   have hσ: w^2 ≤ d*u:=by
      have h:= mul_le_mul_of_nonneg_left (burningSize (H:=H) i).1 (α i).width_pos.le; have hm:=mul_le_mul_of_nonneg_right hz (pow_nonneg (zero_le_one.trans hW) 3);  linarith only [h,hm,pow_le_pow_right₀ hW (by decide:2≤3),sq_nonneg w]
   have hε: w^2 ≤ e*u:=by
      have hY0 : Y₀ ≤ e:= (U).fits.deepExp (Nat.zero_le _); have h: w^2 ≤ Y₀*u:=by
         have h:= mul_le_mul_of_nonneg_left (burningSize (H:=H) i).1 hY₀.le; have hz:1 ≤ w*Y₀:= (div_le_iff₀ hY₀).mp hY; linarith only [h,mul_le_mul_of_nonneg_right hz (pow_nonneg (zero_le_one.trans hW) 3),pow_le_pow_right₀ hW (by decide:2≤3)];
      exact h.trans (mul_le_mul_of_nonneg_right hY0 (Nat.cast_nonneg _))
   have hA : 0≤ F*(4*A^2)+24*A:=by positivity
   have hζ : 0≤F:= Nat.cast_nonneg _
   have hu:=hh; have ha':0≤2*b.direct+2*b.linear+2*A^2:= by linarith only [b.quadratic_pos,b.tail_pos,sq_nonneg A]
   change 0≤ D _+q i ∧ D _+q i≤_ ∧ Real.exp (-d*u)*D _+ Real.exp (-e*u)*q i≤_
   refine ⟨by have he:F*_=F*(2*b.direct+2*b.linear+2*A^2):= rfl; change 0≤ D (2*b.direct+2*b.linear+2*A^2)+_; unfold D; positivity, hs _ ha' hα,?_⟩
   let v:=vanishP U i; have hv: 0≤v:= (Real.exp_pos _).le; have hx':(4*A^2) ≥0:= by positivity
   apply le_trans ?_ (mul_le_mul_of_nonneg_left (hs (4*A^2) hx' hx) hv); rw [mul_add v]; apply add_le_add
   · exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by change -d*u≤ -(w^2); linarith only [hσ])) (show 0 ≤ D (4*A^2) from (by unfold D; positivity))
   exact mul_le_mul_of_nonneg_right (Real.exp_monotone (by change -e*u≤ -(w^2); linarith only [hε])) hδ
lemma tended (Z:H.Selected): ∀ᶠ i:ℕ in atTop,∀ N p,i≤N → Stove.Chart (H.rep N p i) (r i) ((X i)^6) (vanishP U i*(X i)^6) ∧ (Stove.haloFee (H.rep N p i) (r i):ℝ)+1 ≤ 200*(Real.log (X i))^6:=by
   filter_upwards [firebox Y θ Z, treasuryC Y θ Z] with i hi hz N p hm; obtain ⟨hx,hT,hB⟩:= hi N p hm; obtain ⟨-,hC,ht⟩:=hz N p hm; have h:=Stove.tender _ _ hx hT (Z.represents N p i hm|>.good); exact ⟨⟨h.home,h.turn,h.shoots,fun x W=>(h.paid x W).trans hC,h.bill,fun W=>(h.rate W).trans (mul_le_mul_of_nonneg_left ht (by positivity))⟩,hB⟩ -- U notation conflict
end YM.OPE.Therm
