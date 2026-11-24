import YM.OPE.Compatible.Harks.Ere
/-!
# Upper eigen parameters. Recurrence solving.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {r x b c t q:ℝ}
local notation "A!"=> (E→L[ℝ] E)
variable {a f:ℕ→ E}{g:ℕ→ F}{p:ℕ→ E→L[ℝ] E}
abbrev flint (q:ℝ) (_n:ℕ) : A!:= q • 1
lemma scalarHexu (h: Run (flint q) a 0)(hx: 0 ≤ q)(hr:q≤r):Hex r a ‖a 0‖:=by
   intro i; have he:0≤r:=hx.trans hr; induction i with
   | zero=> simp
   | succ i ih=> rw [h,Pi.zero_apply, add_zero]; change ‖q • a i‖≤ _; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hx, pow_succ]; exact (mul_le_mul hr ih (norm_nonneg _) he).trans_eq (by ring)
lemma det (hr:0 ≤ r)(h:r<q)(hx:Run (flint q) a 0)(ht:Hex r a b) : a 0=0:=by
   have hy:0<q:=hr.trans_lt h; have hu(i:ℕ): a i=q^i • a 0:=by
       induction i with
       | zero=> simp
       | succ i ih=> rw [hx,Pi.zero_apply,add_zero]; change q • a i= _; rw [ih,smul_smul,pow_succ']
   have hh(i): ‖a 0‖≤ b*(r/q)^i:=by have he:=ht i; rw [hu i,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hy.le _),mul_comm] at he; rw [div_pow,← mul_div_assoc,le_div_iff₀ (pow_pos hy _)]; exact he
   have hl: Tendsto (fun i:ℕ=> b*(r/q)^i) atTop (𝓝 0):=by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hy.le) ((div_lt_one hy).2 h)).const_mul b
   simpa using (ge_of_tendsto' hl hh)
lemma below [CompleteSpace E](hq:r<q) (hr:0 ≤ r)(hf: Hex r f b): ∃ V:E, Hex r (race (flint q) f V) (b/(q-r)):=by -- remove E0
   let v (j i:ℕ):= q⁻¹^(i+1) • f (j+i); let R (j:ℕ):=∑' i,v j i; have ht: r/q<1:= (div_lt_one (hr.trans_lt hq)).2 hq; have hp:0<q:= hr.trans_lt hq; let z:=r/q; have hz:0 ≤ z:=div_nonneg hr hp.le; let g (j:ℕ):= b*r^j*q⁻¹
   have he(j i):‖v j i‖ ≤ g j*z^i:=by
       dsimp only [v]; rw [norm_smul,Real.norm_eq_abs, abs_of_nonneg (by positivity : 0≤q⁻¹^(i+1))]; apply (mul_le_mul_of_nonneg_left (hf (j+i)) (by positivity:0 ≤q⁻¹^(i+1))).trans_eq; unfold z g; rw [div_eq_mul_inv,mul_pow,pow_add,pow_succ]; ring
   have hx:Summable fun i:ℕ=> z^i:= summable_geometric_of_lt_one hz ht; have hs(j):Summable (fun i=>‖v j i‖):= Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (he j) (hx.mul_left (g j)); let A(j:ℕ):= - R j; have hb: Run (flint q) A f:=by
       intro i; have hy(y:ℕ): v (i+1) y=q • v i (y+1):=by unfold v; rw [smul_smul,pow_succ q⁻¹ (y+1),mul_comm (q⁻¹^(y+1)),← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul, show i+1+y=i+(y+1) by omega]
       have hz:R (i+1)=q • (R i-v i 0):=by
           have hV: R i=v i 0 + ∑' j,v i (j+1):=((hs i).of_norm.sum_add_tsum_nat_add 1).symm.trans (by simp)
           unfold R at *; simp_rw [hV,add_sub_cancel_left,hy]; exact tsum_const_smul'' ..
       change -R (i+1)= q • - R i+_; rw [hz, smul_sub]; have h': q • v i 0=f i:=by simp [v,smul_smul,hp.ne']
       rw [h',smul_neg];abel
   refine ⟨A 0,?_⟩; rw [hb.isRace.symm]; intro i; rw [show A _= - ∑' j,v i j from rfl,norm_neg]; refine (norm_tsum_le_tsum_norm (hs i)).trans (((hs i).tsum_le_tsum (he i) (hx.mul_left (g i))).trans_eq ?_); rw [tsum_mul_left,tsum_geometric_of_lt_one hz ht]; unfold g z; have hh: q-r≠0:=by linarith
   field_simp
lemma scar [CompleteSpace E] (hq:r≠q)(hp:0 ≤ q)(hr:0 ≤ r)(hf: Hex r f b): ∃ V:E,Hex r (race (flint q) f V) (b/|q-r|):=by
    obtain h|h:=hq.lt_or_gt
    · obtain ⟨v,H⟩:= below h hr hf; exact ⟨v,by rw [abs_of_nonneg (sub_nonneg.mpr h.le)]; exact H⟩
    rw [show q-r= -(r-q) from by ring,abs_neg,abs_of_nonneg (sub_nonneg.mpr h.le)]; exact ⟨0,Run.gap h _ hp le_rfl hf (gait (flint q) f 0) (fun i=> by simp [flint,norm_smul,Real.norm_eq_abs,abs_of_nonneg hp]) (by simpa [race] using (div_nonneg hf.price (by linarith : 0 ≤ r-q))) ⟩
end YM.OPE.Hark
