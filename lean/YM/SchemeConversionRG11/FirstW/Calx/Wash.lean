import YM.SchemeConversionRG11.FirstW.Calx.Sails
/-! hypercubic regulator CT bill over local native coordinates (Lift boundary not used). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position SchemeConversionRG11 SchemeConversionRG11.Horizon Deck
open scoped BigOperators Classical ContDiff
variable {G : Gauge} {T : Itinerary} {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R:ℝ}
abbrev Wash := ContDiffBump (0:E4)
def soft (Q: Wash)(v:E4):ℝ:= (Fintype.card Signed:ℝ)⁻¹ * ∑ i:Signed,Q (Ortho.move i.ortho v)
lemma soft_price (Q:Wash): ContDiff ℝ ∞ (soft Q) := by
 unfold soft; refine contDiff_const.mul ?_; apply ContDiff.sum; intro i _; exact Q.contDiff.comp (f:=Ortho.motion i.ortho) (Ortho.motion i.ortho).toContinuousLinearEquiv.contDiff
lemma soft_spin (Q:Wash)(u:Signed)(x:E4): soft Q (Ortho.move u.ortho x)=soft Q x := by
 simp only [soft,← Ortho.move_mul, show ∀ i:Signed,i.ortho*u.ortho=(i*u).ortho from fun i=>(Signed.inclusionO.map_mul i u).symm]; apply congrArg _; exact Equiv.sum_comp (Equiv.mulRight u) (fun s=> Q (Ortho.move s.ortho x))
lemma soft_clear (Q:Wash)(x:E4) (h:‖x‖ ≤ Q.rIn): soft Q x=1 := by
 unfold soft; simp_rw [show ∀ i:Signed,Q (Ortho.move i.ortho x)=1 from fun i=>Q.one_of_mem_closedBall (mem_closedBall_iff_norm.mpr (by rw [sub_zero,Ortho.move_norm]; exact h))]; simp
lemma soft_life (Q:Wash)(x:E4)(h:Q.rOut ≤ ‖x‖): soft Q x=0 := by
 unfold soft; simp_rw [show ∀ i:Signed,Q (Ortho.move i.ortho x)=0 from fun i=>Q.zero_of_le_dist (by rw [dist_zero_right,Ortho.move_norm]; exact h)]; simp
lemma soft_credit (T : Itinerary)(Q:Wash) (R:ℝ) : Credit T R 0 0 (fun i x=> soft Q (Moss T i x)) := by
 have hp:Fintype.card Signed>0:= Fintype.card_pos
 have he :∀ x:E4, ‖soft Q x‖ ≤ 1:=fun x=>by
    unfold soft
    have h (i:Signed): ‖Q (Ortho.move i.ortho x)‖ ≤ 1:= by rw [Real.norm_of_nonneg Q.nonneg]; exact Q.le_one
    rw [norm_mul,Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ (by exact_mod_cast hp)]
    exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=>h i)).trans_eq (by simp))
 refine ⟨1,one_pos,Eventually.of_forall (fun i x _=>?_ )⟩
 simpa only [zpow_zero,mul_one] using he (Moss T i x)
lemma moss_move (T:Itinerary)(s:Signed)(x:Cover)(i:ℕ): Moss T i (s.act x)= Ortho.move s.ortho (Moss T i x) := by
 rw [Signed.ortho_move]; ext j; simp only [Moss, Full.incVec_apply,Signed.act]; split_ifs <;> simp
-- local sector W takes actual q
variable (T G)
def wheelS (r:ℕ) (Q:Wash) : Sky G ℤ := ∑ x∈pod T Q.rOut r, ∑ i:Ticket,∑ j:Ticket, soft Q (Moss T r x) • tower G x (icon (fresh i) (fresh j))
lemma wash_eq (r:ℕ)(Q:Wash)(A B C:Field4 G): wheelS G T r Q A B C=∑ x∈pod T Q.rOut r, soft Q (Moss T r x)*∑ i:Ticket,∑ j:Ticket,tower G x (icon (fresh i) (fresh j)) A B C := by simp only [wheelS,LinearMap.sum_apply, LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]
lemma wash_spin (s:Signed)(r:ℕ)(Q:Wash)(A B C:Field4 G): wheelS G T r Q (Bare.wideLink G s A) (Bare.wideLink G s B) (Bare.wideLink G s C)=wheelS G T r Q A B C := by
 let K(s:Signed)(x:Cover):= soft Q (Moss T r (s.act x)); have hv(s:Signed)(x:Cover): K s x= soft Q (Moss T r x):= by unfold K; rw [moss_move,soft_spin]
 simp_rw [wash_eq,gear_push]; have ht (x:Cover)(s:Signed) : s.act x∈ pod T Q.rOut r ↔ x∈ pod T Q.rOut r:= by rw [in_pod,in_pod, Jam,Jam,moss_move,Ortho.move_norm]
 refine Finset.sum_bij (fun x _=>s.act x) (fun x hx=>(ht x s).mpr hx) (fun i _ j _ h=>s.actEquiv.injective h) (fun x hx=>⟨_,(ht x s⁻¹).mpr hx, by simp⟩) (fun x _=>by rw [moss_move,soft_spin])
variable {G T}
def tin (G:Gauge)(n:Side)(a:Who G 6): Field4 G:= terms (0:Site n) (canal a.val 0)
lemma spin_tin (s:Signed)(a:Who G 6)(n:Side): ∑ k:Who G 6, accord (swayL G 6 s) a k • Bare.wideLink G s (tin G n k) = tin G n a := by
 simp_rw [tin,terms_pull,Signed.act_zero,←map_smul,←map_sum]; apply congrArg _; have h:= TintK _ _ 0 _ (spin_pl G 6 s (X:=Per n) 1) (turn_branch s) a; simpa only [river,one_pow, inv_one,one_smul,map_sum,map_smul] using h
lemma tone_tin (u:G.El)(a:Who G 6)(n:Side): ∑ k:Who G 6, accord (paintL 6 u) a k • putting u (tin G n k)=tin G n a:= by
 simp_rw [tin,show ∀ A:FullT G n,putting u (terms (0:Site n) A)=terms 0 (putting u A) from fun _=>rfl,← map_smul,←map_sum]; apply congrArg _; have h:= TintK _ _ 0 1 (tint_pl 6 u (0: Site n) 1) (color_branch u) a; simpa only [river,one_pow,inv_one,one_smul,map_sum,map_smul] using h
end YM.RG11.FirstW
