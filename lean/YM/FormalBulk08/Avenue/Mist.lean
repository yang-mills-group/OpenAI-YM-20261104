import YM.FormalBulk08.Avenue.Grid
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
variable {n:Side}
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rock (f: Site n→E)(x:Pitch):= ∑ v:Site n,(block n (Lattice.lift v)).indicator (fun _ : Pitch=> f v) x
omit [NormedSpace ℝ E] in
lemma rock_pane (f:Site n→E){x:Pitch}{v:Site n}(h:x∈block n (Lattice.lift v)): rock f x=f v := by
    rw [rock,Finset.sum_eq_single v]; exact indicator_of_mem h _;intro p _ hp; exact indicator_of_notMem (fun hx=> hp (lift_inj ((slot_map .. |>.mp hx).symm.trans ((slot_map ..).mp h)))) _; simp
omit [NormedSpace ℝ E] in
lemma rock_nil (f:Site n→E){x:Pitch}(h:∀ i:Site n,x∉block n (Lattice.lift i)):rock f x=0:= Finset.sum_eq_zero fun i _=>indicator_of_notMem (h i) _
omit [NormedSpace ℝ E] in
lemma pillar (x:Cover)(a:E): Integrable ((block n x).indicator (fun _=>a)):= IntegrableOn.integrable_indicator (integrableOn_const (square_finite n x)) (block_meas _ _)
omit [NormedSpace ℝ E] in
lemma rock_meas (f:Site n→E): Integrable (rock f):=integrable_finsetSum _ fun i _=> (pillar _ (f i))
variable [CompleteSpace E]
lemma rock_w (f:Site n→E): (∫ x:Pitch, rock f x)=(hop n)^4 •∑ i:Site n,f i:= by
    unfold rock; rw [integral_finsetSum _ (fun i _=> (pillar _ (f i))), Finset.smul_sum]; exact Finset.sum_congr rfl fun i _=> by rw [MeasureTheory.integral_indicator (block_meas ..),MeasureTheory.setIntegral_const,square_price]

def province (x:Pitch):= (ball (0:Pitch) (4*Real.pi)).indicator (fun p=> 4*(‖p‖^2)⁻¹) x
lemma province_pos (x:Pitch):0≤ province x:= by by_cases h: x∈ ball (0:Pitch) (4*Real.pi) <;> simp only [province,indicator,h] <;> simp only [reduceIte] <;> positivity
lemma prim_province : Integrable province:= by
    refine IntegrableOn.integrable_indicator ((integrableOn_ball_of_norm_le_rpow (f:= (fun p:Pitch=>(‖p‖^2)⁻¹)) (by simp : 1 ≤ Module.finrank ℝ Pitch) (C:=1) (α:=2) (r:=4*Real.pi) (by norm_num [Pitch]) (.of_forall (?_)) (by fun_prop)).const_mul (4:ℝ))  measurableSet_ball -- `ex`
    intro x; rw [Real.rpow_neg (norm_nonneg x),one_mul,show (2:ℝ)=((2:ℕ):ℝ) from by norm_num,Real.rpow_natCast,Real.norm_of_nonneg (by positivity)]
omit [CompleteSpace E] [NormedSpace ℝ E] in
lemma province_payment {C:ℝ}(f:Site n→E)(h:∀ i: Site n, i ≠ 0→ ‖f i‖ ≤ C/‖tone n (Lattice.lift i)‖^2)(hc:0≤C)(hf:f 0=0)(x:Pitch)(hx:x≠0): ‖rock f x‖≤ C*province x:= by
    have hp : 0≤C*province x:= mul_nonneg hc (province_pos x); by_cases ht:∃ i:Site n,x∈block n (Lattice.lift i); swap
    · push Not at ht; rw [rock_nil f ht,norm_zero]; exact hp
    obtain ⟨i,hi⟩:=ht; rw [rock_pane f hi]; by_cases hv:i=0;subst i; rw [hf,norm_zero]; exact hp
    let y:=tone n (Lattice.lift i); have hy:hop n ≤ ‖y‖ := hefty i hv
    have ha := enjoys x n _ hi; change dist x y≤ hop n at ha
    have hb : ‖x‖≤ ‖y‖+hop n:=by rw [dist_eq_norm] at ha; linarith only [ha,norm_sub_norm_le x y]
    have hh : 0<‖x‖:= norm_pos_iff.mpr hx; have heq : 0<‖y‖:=(pitch_high n).trans_le hy
    rw [province,indicator_of_mem (?_ : x∈ball (0:Pitch) (4*Real.pi))]; swap
    · rw [mem_ball_zero_iff]
      linarith only [hb,hy,(show ‖y‖≤Real.pi from inner_reflected i), Real.pi_pos]
    apply le_trans (h i hv); rw [div_eq_mul_inv]; change _ ≤ C*(4*_); apply mul_le_mul_of_nonneg_left _ hc
    change (‖y‖^2)⁻¹ ≤ _; field_simp; nlinarith [pow_le_pow_left₀ hh.le (show ‖x‖≤ 2*‖y‖ by linarith only [hy,hb]) 2]
lemma rock_price (C:ℝ) (f:Site n→E)(h:∀ i: Site n,i≠0→ ‖f i‖≤ C/ ‖tone n (Lattice.lift i)‖^2)(hc:0≤C)(hf:f 0=0) : ‖(hop n)^4 • (∑ i:Site n,f i)‖ ≤ C*∫ x:Pitch,province x := by
   rw [←rock_w, ←integral_const_mul]; exact norm_integral_le_of_norm_le (prim_province.const_mul _) (Eventually.mono (volume.ae_ne 0) (province_payment f h hc hf · ·))

-- tendsto all native sides
omit [CompleteSpace E] [NormedSpace ℝ E] in
lemma point_lit (f:Pitch→E)(hp : ∀ x:Pitch,x≠0→‖x‖<Real.pi→ ContinuousAt f x)(x:Pitch)(hx:x ≠ 0)(he:‖x‖ ≠ Real.pi): Tendsto (fun n:Side=>rock (fun i:Site n=> f (tone n (Lattice.lift i))) x) atTop (𝓝 ((Metric.ball 0 Real.pi).indicator f x)) := by
   rcases lt_or_gt_of_ne he with he|he
   · rw [indicator_of_mem (mem_ball_zero_iff.mpr he)]; apply ((hp x hx he).tendsto.comp (guided x)).congr'; filter_upwards [veil x he] with n hn; rw [rock_pane _ (v:=wrap n (meterTile x n)),hn];rfl
     rw [hn]; exact inside x n
   rw [indicator_of_notMem (fun (h:x∈ball 0 Real.pi)=> (not_lt.mpr he.le) (mem_ball_zero_iff.mp h))]; refine tendsto_const_nhds.congr' ((bleak x he).mono (fun n hn=> (rock_nil _ hn).symm))
lemma rock_lim {f:Pitch→E}(hh:f 0=0)(h : ∀ x:Pitch,x ≠ 0→‖x‖<Real.pi→ ContinuousAt f x) (C:ℝ)(hc:0≤C)(hb : ∀ n:Side,∀ i:Site n,i≠0→ ‖f (tone n (Lattice.lift i))‖ ≤ C/‖tone n (Lattice.lift i)‖^2) :
   IntegrableOn f (ball 0 Real.pi) ∧ Tendsto (fun n:Side=> (hop n)^4 •∑ i:Site n,f (tone n (Lattice.lift i))) atTop (𝓝 (∫ p:Pitch in ball 0 Real.pi, f p)):= by
    let F n:= fun i:Site n=> f (tone n (Lattice.lift i)); let G:Pitch→E:=(ball 0 Real.pi).indicator f; let M(x:Pitch):= C*province x
    have hm: Integrable M:= prim_province.const_mul _
    have he (p:Pitch) (he:p≠0) (n:Side): ‖rock (F n) p‖≤ M p:= province_payment (F n) (hb n) hc (show F n 0=0 from ?_) p he
    swap
    · rw [show F n 0=f 0 from congr_arg f (show tone n (Lattice.lift (0:Site n))=0 from funext fun i=>by simp [tone, lift_origin n]),hh]
    have ht: ∀ᵐ x:Pitch, Tendsto (fun n:Side=>rock (F n) x) atTop (𝓝 (G x)):= by
        filter_upwards [volume.ae_ne 0,compl_mem_ae_iff.mpr (Measure.addHaar_sphere volume (0:Pitch) Real.pi)] with x hx hE
        exact point_lit f h x hx (by simpa [mem_sphere] using hE)
    have hi : Integrable G volume:= hm.mono' (aestronglyMeasurable_of_tendsto_ae (β:=E) atTop (fun n=>(rock_meas (F n)).aestronglyMeasurable) ht) (by filter_upwards [volume.ae_ne 0,ht] with x hx h'; exact le_of_tendsto h'.norm (.of_forall (he x hx)))
    refine ⟨(integrable_indicator_iff measurableSet_ball).mp hi,?_⟩
    have hv:= tendsto_integral_filter_of_dominated_convergence M (Eventually.of_forall (fun n=>(rock_meas (F n)).aestronglyMeasurable)) (.of_forall (fun n=>(volume.ae_ne 0).mono (fun x hx=> he x hx n))) hm ht
    unfold G at hv; simp_rw [rock_w,MeasureTheory.integral_indicator measurableSet_ball] at hv; exact hv
end YM.FormalBulk08.Avenue
