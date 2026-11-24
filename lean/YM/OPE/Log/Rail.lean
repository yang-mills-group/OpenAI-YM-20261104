import YM.OPE.Log.Grid
import YM.OPE.Exchange.Coherence
import YM.OPE.Polar.Supervise
/-! # Mesh choices to pay contour rendering -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open Function Filter MeasureTheory Metric Lattice RG Polar
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{ι I:Type}[Fintype I] {l:Filter ι}{T r:ι→ℝ}{a M η:ℝ} {W r' D}
    {k j m:ι→ℕ}(L:LogPackage C W r' D)(hG:G.Simple){x:ι→ I→E4}
set_option quotPrecheck false
local notation "β"=> C.path.levels.clock.hatBeta
local notation "F"=> C.path.levels.budget
include hG
private lemma peep_cost (hm:Height C.S l T m 1)(ht:Tendsto T l atTop) : ∀ᶠ i in l, (((C.path.levels.budget (m i)).B:ℝ)^2) ≤ T i^16:=by
    let b i:=β (m i); let J:=G.slopeConstant; let a:= C.path.levels.clock.bar; have ha:= C.path.levels.clock.bar_pos; have hJ:= Gauge.slopeConstant_pos hG; filter_upwards [hm.pace.eventually (ge_mem_nhds (show (1:ℝ) < 2 from one_lt_two)), ht.eventually_ge_atTop (a+2*J), ht.eventually_ge_atTop 2] with i hi hT hv
    have hh:0<T i:= zero_lt_two.trans_le hv; have hF: b i ≤ T i^2:=by
       have he:C.S.scale (m i) ≤2*T i:= (div_le_iff₀ hh).mp hi; change a + J*C.S.scale (m i) ≤ _; nlinarith only [mul_le_mul_of_nonneg_left he hJ.le, le_mul_of_one_le_right (show 0 ≤ a from ha.le) (one_le_two.trans hv), mul_le_mul_of_nonneg_right hT hh.le]
    have hp:1 < b i:= C.path.levels.fits.delayed _; have he : ((F (m i)).B:ℝ) ≤ T i^8 := by
       refine le_trans (Nat.ceil_lt_add_one (sq_nonneg (Real.log (b i)))|>.le) ?_; have he:Real.log (b i) ≤ T i^2:= (Real.log_le_self (zero_le_one.trans hp.le)).trans hF; have hg: (Real.log (b i))^2 ≤ (T i^2)^2:= pow_le_pow_left₀ (Real.log_nonneg hp.le) he _; have hu: (2:ℝ) ≤ T i^4:= hv.trans ((pow_one _).symm.trans_le (pow_le_pow_right₀ (one_le_two.trans hv) (by norm_num))); nlinarith only [hg,hu,sq_nonneg (T i^4 - 1)]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) he 2).trans_eq (by ring)
variable (hr:Tendsto r l (𝓝[>] (0:ℝ)))
local notation "T'"=> (fun i=>run (r i))
include hr
private lemma short_len [DecidableEq I] {g:ι→I→ Cover} (hm:Height C.S l T' j 1)(ht:∀ᶠ i in l, C.S.a (j i)< r i/T' i^32)(h:0<η): ∀ᶠ i in l,2*C.S.a (j i)* (((F (j i)).B:ℝ)^2) < η*r i:=by
    have hT:= run_towards hr; filter_upwards [ht,peep_cost hG hm hT,hT.eventually_ge_atTop (2/η+1),hT.eventually_ge_atTop 2,(loglife hr).pos] with i hi he hT hh hr; let u:= T' i; let v i:= C.S.a (j i)
    have hu:1 < u:= one_lt_two.trans_le hh; have hy:2/η < u:= by change 2/η+1 ≤ u at hT; linarith only [hT];
    calc _ ≤ 2*v i*u^16 := mul_le_mul_of_nonneg_left he (mul_nonneg zero_le_two (C.S.a_pos _).le)
         _ ≤ 2*(r i/u^32)*u^16:= by gcongr
         _ < _:=by have he: 2 < η*u^16:=by rw [← div_lt_iff₀' h]; exact hy.trans_le ((pow_one u).symm.trans_le (pow_le_pow_right₀ hu.le (by norm_num))); -- orientation lemma
                   have hf: (r i/u^32)*u^16= r i/u^16:=by field_simp -- `ring`
                   rw [mul_assoc,hf, ← mul_div_assoc, div_lt_iff₀ (pow_pos (by linarith only [hu]) _)]; linarith only [mul_lt_mul_of_pos_right he hr]
include L
lemma enough_spans : ∃ m j:ι→ℕ, Height C.S l T' m 1 ∧ Height C.S l T' j 1 ∧
    (∀ᶠ i in l, r i*T' i ≤ C.S.a (m i+1) ∧ m i+1< j i ∧ C.S.a (j i)< r i/T' i^32) ∧ ValueStamp l T' (fun i=>r i/C.S.a (m i)) ∧ ValueStamp l T' (fun i=> r i/C.S.a (j i)):=by
    have hT:=run_towards hr; have he:= Wallet.clock hT; let z:= T'; let u i:=r i /z i^32; have hu : RateIs l T' u (-1):=((loglife hr).div (he.power 32)).swap (by simp); let w i:=r i*z i; have hw: RateIs l T' w (-1):=((loglife hr).mul he).swap (by ring); obtain ⟨m,hm,hM,hξ⟩:= bracket_down hT hw (hw.tends neg_one_lt_zero hT) L; obtain ⟨j,hj,hJ,hρ⟩:= bracket_up hT hu (hu.tends neg_one_lt_zero hT) L
    refine ⟨m,j,hm,hj,?_,?_,?_⟩
    · filter_upwards [hM,hJ,hT.eventually_ge_atTop 1,(loglife hr).pos] with i hi he hx hp; have ht: u i ≤ w i:= (div_le_self (a:=r i) hp.le (one_le_pow₀ hx)).trans (le_mul_of_one_le_right hp.le hx)
      exact ⟨hi,C.S.strictAnti.lt_iff_gt.mp (he.1.trans_le (ht.trans hi)),he.1⟩
    · apply (hξ.div (ValueStamp.atT hT)).congr; filter_upwards [hT.eventually_gt_atTop 0] with i hi; unfold w z; have hx:= C.S.a_pos (m i); field_simp
    apply (hρ.mul ((ValueStamp.atT hT).pow hT 32)).congr; filter_upwards [hT.eventually_gt_atTop 0] with i hi; unfold u z; have hx:= C.S.a_pos (j i); field_simp
local notation "T0"=> C.S.gridPoint
omit L
lemma subPlot [DecidableEq I] {P:ι→I→ Cover}(he:0<η) (hk:Height C.S l T' k (1/2))(hm:Height C.S l T' m 1)(hj:Height C.S l T' j 1) (hv:∀ᶠ i in l, r i*T' i ≤ C.S.a (m i+1) ∧ m i+1 < j i ∧ C.S.a (j i)< r i/T' i^32) (hZ:∀ᶠ i in l, WithinRoom (r i) M η (C.S.gridPoint (j i) ∘ P i) 0) : ∀ᶠ i in l, Plot C (k i) (m i) (j i) (P i):=by
    have hT:=run_towards hr; filter_upwards [hv,hZ,short_len hG hr (g:=P) hj (hv.mono fun i hi=> hi.2.2) he, (loglife hr).pos,hT.eventually_gt_atTop (8*M),hk.earlier (by norm_num) hT hm] with i hv hZ he hp hv' hh; refine ⟨fun p=>?_, fun j k hj=> he.trans_le (hZ.spaced j k hj), hh.le,hv.2.1.le⟩
    have hk:= hZ.span p; rw [sub_zero] at hk; exact (mul_le_mul_of_nonneg_left hk (by norm_num: (0:ℝ)≤8)).trans_lt ((show 8*(M*r i)<r i*T' i from by nlinarith only [mul_lt_mul_of_pos_right hv' hp]).trans_le hv.1)
end YM.OPE.Log
