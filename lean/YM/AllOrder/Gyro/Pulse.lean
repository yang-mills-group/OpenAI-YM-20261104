import YM.AllOrder.Gyro.Wave
/-! Leading response of the regular part with one common health window before taking the
 cutoff jet. The window can depend on period; the final anchor bounds do not. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Gyro.Soft
open Function Filter Set Lattice Wilson RG AnalyticBridge.VerifiedReset
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {p : BudgetPoint} {δ : ℝ} {A : Activities G n}

variable {X:Support n}{o:Site n}{z:ℝ}
/- Repaired proofs from Pert/Kinetic/Densities.lean (autoImplicit) -/
lemma payment_sum (h : A.EBound p δ) : ∃ b:ℕ→ℝ, (∀ i,p.supBounds (A.reg i).site (A.reg i).support (A.E i) (b i)) ∧
    (Summable fun i=>p.mass (A.reg i).support (b i)) ∧ (∑' i,p.mass (A.reg i).support (b i)) ≤ Fintype.card (Site n)*δ := by
   obtain ⟨b,h1,h⟩:=h
   let q x i:= if (A.reg i).site=x then p.mass (A.reg i).support (b i) else 0
   have hq := summable_sum (s:=Finset.univ) fun (i : Site n) _ => (show Summable (q i) from (h i).2.1)
   have he : ∀ i, p.mass (A.reg i).support (b i) = ∑ x, q x i := fun i=> by simp [q]
   refine ⟨b,h1,(by rw [funext he];exact hq),?_⟩
   rw [funext he] 
   rw [Summable.tsum_finsetSum]
   calc _ ≤ ∑ _x:Site n,δ := Finset.sum_le_sum fun i _=> (h i).2.2
        _ = _ := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
   exact fun i _=>(h i).2.1

lemma rays_free (r : ℝ) (hr : 0 < r) (v : Directions G n) : ∀ᶠ t in 𝓝 (0:ℝ), flags r (line v t)=∅ := by
   have hh (f : Face (Per n)) : ∀ᶠ t in 𝓝 (0:ℝ), G.chord (faceValue (line v t) f) < r := by
      have ht : Continuous fun t : ℝ=> G.chord (faceValue (line v t) f) := by unfold line faceValue increment; fun_prop
      have hl : G.chord (faceValue (line v 0) f)=0 := by rw [line_zero]; unfold faceValue; change G.chord (travel _ _ [_,_,_,_])=_; simp [travel,Step.read,G.chord_one] 
      exact ht.continuousAt.eventually ((Iio_mem_nhds (by exact hl.trans_lt hr)) : ∀ᶠ _ in 𝓝 _, _)
   filter_upwards [eventually_all.mpr hh] with t ht
   apply Finset.eq_empty_iff_forall_notMem.mpr
   intro x hs; obtain ⟨f,h0,h1⟩:= (flags_spec ..).mp hs; exact (ht f).not_ge h1.le 

lemma along (f : Pot G n) (hf : p.Regular X f) (v : Directions G n) (l : List (Directions G n)) (t : ℝ) (h : Healthy p.threshold X (line v t)) (hl : l.length < p.order) : HasDerivAt (fun s=> leftDerivs f l (line v s)) (leftDerivs f (v::l) (line v t)) t := by

   have he s : increment (line v t) (s • v)=line v (s+t) := by
      funext e; apply G.mat_injective; simp only [increment,line,Pi.one_apply,mul_one,Gauge.mat_mul,Gauge.mat_lieExp,Pi.smul_apply,add_smul,map_add,map_smul]
      haveI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
      exact NormedSpace.exp_add_of_commute (((Commute.refl _).smul_left s).smul_right t) |>.symm
   have hd:= (hf.hasDerivs _ h v l hl)
   simp_rw [he] at hd
   have hd := show HasDerivAt _ _ (t-t) from (sub_self t).symm ▸ hd
   have hd' := hd.comp (x:=t) (h:=fun s:ℝ => s-t) (hasDerivAt_id' t |>.sub_const t)
   simpa only [Function.comp_def,sub_add_cancel, mul_one] using hd'


lemma line_bound (v : Directions G n) {a t : ℝ} (hu : |t| < a) (hv : ∀ x, |x| < a → Healthy p.threshold X (line v x))
     (f : Pot G n) (h : p.Regular X f) (he : p.supBounds o X f z) (hz : f 1 = 0) (hG : G.Simple) (hD : p.dirBound o v) :
     ‖f (line v t)‖ ≤ z*t^2 := by
   let Φ s x:= leftDerivs f [v] (line v (x*(s*t)))
   have hP(s x:ℝ)(hs:s∈Icc 0 1)(hx:x∈Icc 0 1)(l : List (Directions G n))(hl:l.length<p.order): HasDerivAt (fun u=> leftDerivs f l (line v (u*(s*t)))) ((s*t)*leftDerivs f (v::l) (line v (x*(s*t)))) x := by
      apply ((along f h v l _ ?_ hl).comp x ((hasDerivAt_id' x).mul_const (s*t))).congr_deriv ?_
      · exact hv _ ((show |x*(s*t)| ≤ |t| from by rw [abs_mul,abs_mul,abs_of_nonneg hx.1,abs_of_nonneg hs.1,←mul_assoc]; nlinarith only [hx.1,hx.2,hs.1,hs.2, mul_le_mul (show x ≤ 1 from hx.2) (show s≤1 from hs.2) hs.1 (show 0≤(1:ℝ) by positivity), show 0≤|t| by positivity]).trans_lt hu) 
      simp [mul_comm]
   have hF (s:ℝ)(hs:s∈Icc 0 1):‖Φ s 1‖ ≤ |s*t| *z := by
      let K x:= (s*t)*leftDerivs f [v,v] (line v (x*(s*t)))
      have hf (x:ℝ)(hx:x∈Icc 0 1): HasDerivWithinAt (Φ s) (K x) (Icc 0 1) x := (hP s x hs hx [v] (show 1<p.order by linarith only [p.order_ge])).hasDerivWithinAt
      have h0 : leftDerivs f [v] 1=0 := by
         change deriv (fun t => f (increment 1 (t•v))) 0=0
         have H:= Push.side (germ f) ((germ_diff (p:=p) h).differentiableAt (by decide)) v
         exact H.deriv.trans (by rw [flat_critical hG h]; rfl)
      have he':= norm_image_sub_le_of_norm_deriv_le_segment_01' hf (C:=|s*t| *z) fun x hx=>by
         unfold K; rw [norm_mul,Real.norm_eq_abs (s*t)]; apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
         refine he.2 _ (hv _ ((show |x*(s*t)| ≤ |t| by have e := hx; rw [abs_mul, abs_of_nonneg hx.1, abs_mul,abs_of_nonneg hs.1]; have H := mul_le_mul hx.2.le hs.2 hs.1 (zero_le_one); nlinarith only [mul_le_mul_of_nonneg_right H (abs_nonneg t)]).trans_lt hu)) _ (show 2≤p.order by linarith only [p.order_ge]) ?_
         simp_all
      simpa [Φ,line_zero,h0] using he'
   let V x:= f (line v (x*(1*t)))
   have hU (x:ℝ)(hx:x∈Icc 0 1): HasDerivWithinAt V ((1*t)*Φ 1 x) (Icc 0 1) x := (hP 1 x (by simp) hx [] (show 0 < p.order by linarith only [p.order_ge])).hasDerivWithinAt
   have he':= norm_image_sub_le_of_norm_deriv_le_segment_01' hU (C:=z*t^2) fun x hx=>by
      rw [one_mul, norm_mul]; refine (congrArg (‖t‖ * ·) (show ‖Φ 1 x‖=‖Φ x 1‖ by simp [Φ])).le.trans ?_ 
      apply le_trans (mul_le_mul_of_nonneg_left (hF x (Ico_subset_Icc_self hx)) (norm_nonneg _))
      rw [Real.norm_eq_abs,abs_mul, abs_of_nonneg hx.1]
      have hz:=he.1
      calc _ = x*(t^2)*z := by rw [←sq_abs t]; ring
           _ ≤ 1*(t^2)*z := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx.2.le (sq_nonneg t)) hz
           _ = z*t^2 := by ring
   simpa [V,line_zero,hz] using he'

end YM.AllOrder.Gyro.Soft
