import YM.SchemeConversionRG11.FirstW.Calx.Huts
/-! Native credits across shrinking relative-support. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Pert.Align Laurent
open scoped BigOperators Classical
variable {T : Itinerary} {E F G I : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] {R r : ℝ} {u v a b : ℤ}
def Credit (T: Itinerary) (r : ℝ) (a b : ℤ) (f:ℕ → Cover → E) := ∃ C>0,∀ᶠ i in atTop,∀ x:Cover,Jam T r i x → ‖f i x‖≤ C*T.gap i^a * stepY x^b
variable {f g : ℕ → Cover→ E}{w:ℕ → Cover→ F}
lemma Credit.weaken (h:Credit T r a b f)(hb:b≤u)(hr:R≤r): Credit T R a u f:=by
 obtain ⟨C,hc,H⟩:=h; refine ⟨C,hc,H.mono fun i hi x hx=> le_trans (hi x (le_trans hx hr)) ?_⟩; gcongr; · have ht:=T.positive i; positivity
 exact unit_stepY x
lemma Credit.badal {a':ℤ}(h:Credit T r a b f) (he: a'≤a): Credit T r a' b f := by
 obtain ⟨C,hc,H⟩:=h; refine ⟨C,hc,?_⟩; filter_upwards [H,T.cutoff.eventually (ge_mem_nhds (by norm_num:(0:ℝ)<1))] with i hi hy x hx
 refine (hi x hx).trans (mul_le_mul_of_nonneg_right ?_ (zpow_nonneg (zero_le_one.trans (unit_stepY _)) _)); refine mul_le_mul_of_nonneg_left ?_ hc.le; have hh := zpow_le_zpow_right₀ (one_le_inv₀ (T.positive i) |>.2 hy) (neg_le_neg he); simpa only [zpow_neg,inv_zpow,inv_inv] using hh
lemma Credit.drift (h:Credit T r a b f)(hp:R<r)(z:Cover): Credit T R a b (fun i x=>f i (x+z)):= by
 obtain ⟨C,hp',H⟩:=h; let Q:=1+stepY z; have hQ:0<Q:=by unfold Q; linarith only [unit_stepY z] -- semicolon
 have q (x:Cover): stepY (x+z)^b ≤ (Q^(Int.natAbs b))*stepY x^b := by
   cases b with
   | ofNat b=>
    have hv : stepY (x+z) ≤ Q*stepY x := (sum_stepY x z).trans (by unfold Q; nlinarith [unit_stepY x,unit_stepY z])
    erw [show (Int.ofNat b)=(b:ℤ) from rfl,Int.natAbs_natCast,zpow_natCast,zpow_natCast,←mul_pow]; exact pow_le_pow_left₀ (zero_le_one.trans (unit_stepY _)) hv _
   | negSucc d=>
    have he : stepY x ≤ Q*stepY (x+z):=le_trans (show stepY x≤ stepY (x+z)+stepY z from by simpa only [add_neg_cancel_right,stepY_neg] using sum_stepY (x+z) (-z)) (by unfold Q; nlinarith only [unit_stepY z,unit_stepY (x+z)])
    have h := pow_le_pow_left₀ (zero_le_one.trans (unit_stepY x)) he (d+1); rw [mul_pow] at h
    rw [show (Int.negSucc d)=-((d+1:ℕ):ℤ) from rfl, zpow_neg,zpow_natCast,zpow_neg,zpow_natCast,Int.natAbs_neg,Int.natAbs_natCast, ←div_eq_mul_inv, le_div_iff₀ (pow_pos (zero_lt_one.trans_le (unit_stepY _)) _), inv_mul_le_iff₀ (pow_pos (zero_lt_one.trans_le (unit_stepY _)) _)]; linarith only [h]
 refine ⟨C*Q^b.natAbs,by positivity,(H.and (birthM (T:=T) hp z)).mono fun i hi x hx=>?_⟩
 have ht:= T.positive i; exact (hi.1 (x+z) (hi.2 x hx)).trans (le_trans (mul_le_mul_of_nonneg_left (q x) (by positivity)) (le_of_eq (by ring)))
lemma Credit.evolve (h:Credit T R a b f)(e:Credit T R a b g) : Credit T R a b (fun i x=> f i x+g i x):=by
 obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,B⟩:=e; refine ⟨C+D,by positivity,(H.and B).mono fun i hi x hx=>?_⟩; exact (norm_add_le ..).trans ((add_le_add (hi.1 x hx) (hi.2 x hx)).trans (le_of_eq (by ring)))
lemma Credit.less (h:Credit T R a b f)(e:Credit T R a b g) : Credit T R a b (fun i x=> f i x-g i x):=by
 obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,B⟩:=e; refine ⟨C+D,by positivity,(H.and B).mono fun i hi x hx=>?_⟩; exact (norm_sub_le ..).trans ((add_le_add (hi.1 x hx) (hi.2 x hx)).trans (le_of_eq (by ring)))
lemma Credit.pure : Credit T R a b (fun _ _=>(0:E)):= ⟨1,one_pos,Eventually.of_forall fun i x _=>by have h:=T.positive i; have ht:=zero_lt_one.trans_le (unit_stepY x); rw [norm_zero]; positivity⟩
lemma Credit.owed {f:I→ℕ → Cover→ E} (s:Finset I)(h:∀ i∈s,Credit T R a b (f i)): Credit T R a b (fun i x=>∑ j∈s,f j i x) := by
 induction s using Finset.induction with | empty=> simp only [Finset.sum_empty]; exact Credit.pure | insert c q he ih=>simp only [Finset.sum_insert he]; exact Credit.evolve (h _ (Finset.mem_insert_self ..)) (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))
section bilinears
variable [NormedSpace ℝ E][NormedSpace ℝ F][NormedSpace ℝ G]
lemma Credit.fixed (h:Credit T R a b f) (s:ℝ): Credit T R a b (fun i x=>s • f i x) := by
 by_cases e:s=0; · subst s; simp only [zero_smul]; exact Credit.pure
 obtain ⟨C,hC,H⟩:=h; refine ⟨‖s‖*C,mul_pos (norm_pos_iff.mpr e) hC,H.mono fun i hi x hx=>?_⟩
 rw [norm_smul]; exact (mul_le_mul_of_nonneg_left (hi x hx) (norm_nonneg _)).trans_eq (by ring)
lemma Credit.time (h:Credit T R a b f)(r:ℤ): Credit T R (r+a) b (fun i x=>T.gap i^r • f i x):=by
 obtain ⟨C,hC,H⟩:=h; refine ⟨C,hC,H.mono fun i hi x hx=>?_⟩
 have ht:=T.positive i; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact (mul_le_mul_of_nonneg_left (hi x hx) (by positivity)).trans_eq (by rw [zpow_add₀ ht.ne']; ring)
lemma Credit.pays (p: Credit T R a b f)(h : Credit T R u v w)(L:E→L[ℝ] F→L[ℝ] G): Credit T R (a+u) (b+v) (fun i x=> L (f i x) (w i x)):=by
 obtain ⟨C,hC,H⟩:=p; obtain ⟨D,hD,E⟩:=h; let M := 1+‖L‖; have hM:0<M:= by unfold M; positivity
 refine ⟨C*D*M,by positivity,(H.and E).mono fun i hi x hx=>?_⟩
 have hv:= zero_lt_one.trans_le (unit_stepY x); have ht:=T.positive i
 calc _ ≤ ‖L‖*‖f i x‖*‖w i x‖ := (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _))
      _ ≤ M*(C*T.gap i^a * stepY x^b)*(D*T.gap i^u * stepY x^v):=mul_le_mul (mul_le_mul (by unfold M; linarith) (hi.1 x hx) (norm_nonneg _) hM.le) (hi.2 x hx) (norm_nonneg _) (by positivity)
      _ = _ := by rw [zpow_add₀ ht.ne',zpow_add₀ hv.ne']; ring
end bilinears
-- supercritical local continuity envelope
lemma faint_step {p:ℕ → Cover}{x:E4}(he:Harbor T p x)(hx:x≠0): ∃ C>0,∀ᶠ i in atTop,C ≤ Foot T i (p i) := by
 have h:=norm_pos_iff.mpr hx; refine ⟨‖x‖/4,by positivity,(Tendsto.norm he|>.eventually (le_mem_nhds (by linarith only [h]: ‖x‖/2 < ‖x‖))).mono fun i hi =>?_⟩
 change _≤ ‖Moss T i (p i)‖ at hi; have hp := yard_fromE (p i); unfold Foot stepY; unfold Moss at hi; rw [mover_norm _ (T.positive _).le] at hi; nlinarith only [T.positive i,h,hi,hp]
lemma drop_far [NormedSpace ℝ E] (hf:Credit T R 0 (-4) f) (he:Lives T R f) : let K (i:ℕ)(x:Cover):= (T.gap i ^3)⁻¹ • f i x; NearCost T K ∧ Hollow T K (0:E4→E) := by
 intro K; obtain ⟨C,hc,H⟩:=hf
 have hp : ∀ᶠ i in atTop,∀ x: Cover, (Foot T i x)^4*‖K i x‖≤ C*T.gap i := (H.and he).mono fun i hi x=>by
   have hu:=zero_lt_one.trans_le (unit_stepY x); have ht:=T.positive i; by_cases h: f i x=0; · simp only [K,h,smul_zero,norm_zero,mul_zero]; positivity
   have hl := hi.1 x (hi.2 x h); dsimp only [K]; rw [norm_smul,Real.norm_of_nonneg (by positivity)]; unfold Foot; grw [hl];
   · rw [zpow_zero, zpow_neg,zpow_ofNat]; field_simp; apply le_of_eq; ring
 refine ⟨⟨C,hc,hp.mono fun i hi x=>?_⟩,fun x hx p h=>?_⟩
 · have ht:= T.positive i; have he : T.gap i ≤ Foot T i x:= le_mul_of_one_le_right ht.le (unit_stepY _); apply le_of_mul_le_mul_right (a:=T.gap i) _ ht
   refine le_trans (mul_le_mul_of_nonneg_left he (by have h:=ht.trans_le he; positivity)) ?_; linarith only [hi x]
 have e:=hp.mono fun i hi=> hi (p i); obtain ⟨B,hb,L⟩:=faint_step h hx
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ((e.and L).mono fun i hi=>show ‖K i (p i)‖ ≤ C*T.gap i /B^4 from ?_) ?_
 · rw [le_div_iff₀ (pow_pos hb 4), mul_comm]; exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.le hi.2 _) (norm_nonneg _)) hi.1
 exact (by simpa only [mul_zero, zero_div] using (T.cutoff.const_mul C).div_const (B^4))
end YM.RG11.FirstW
