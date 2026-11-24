import YM.Contacts.Model.Echo
/-! Transition-scaled local germs & direction prices. (Not contact germs!)
 Scales are literal transaction measurements. Using Rush sequences also admits post-parameter
 amplification; motions/path gauges not compared along the sequence (dimension even varies).
 Keep powers at fixed receipt. No covariance comparisons.
 -/
namespace YM.Contacts.Loom
open Function Filter Set Finset Metric
open Lattice RG Wilson PhysicalNext.Repeat Pressure ConnectedActivityE6 Blaze
open MeasureTheory Pulse
open scoped Topology InnerProductSpace NNReal BigOperators ContDiff Matrix.Norms.Frobenius Interval Classical
noncomputable section
structure Meter where
    β: ℕ→ℝ
    grows : Tendsto β atTop atTop
variable {f g:ℕ→ℝ}{p q r z d:ℝ}{M:Meter}{P:ℕ→ℝ→Prop}
namespace Meter
lemma eventual (M:Meter): ∀ᶠ i in atTop,0<M.β i:= M.grows.eventually_gt_atTop _
abbrev pow (M:Meter)(e:ℝ)(i):= M.β i ^ e
-- use weak property; not strict bigo(β^p)
def Rush (M:Meter)(p:ℝ)(f:ℕ→ℝ): Prop := ∀ q>p, ∀ᶠ i in atTop, ‖f i‖ ≤ M.pow q i
lemma Rush.grounded (h: Rate G L p F) {U:ℕ→ℝ}(he : Tendsto U atTop atTop) (hu:M.β=ᶠ[atTop] fun i=> betaF G (U i) L): M.Rush p (F ∘ U):= by
   intro q hq; filter_upwards [he.eventually (h q hq),hu] with i hi hi'; unfold Meter.pow; rw [hi']; exact hi
lemma absolute (h:M.Rush p f): M.Rush p (fun i=> |f i|):= fun q hq=> (h q hq).mono fun i hi=> by simpa using hi
namespace Rush
lemma mono (h:M.Rush p f)(hp:p≤q): M.Rush q f:= fun _ hv=> h _ (hp.trans_lt hv)
lemma view (h:M.Rush p f)(he:∀ᶠ i in atTop, ‖g i‖≤ ‖f i‖): M.Rush p g:= fun _ hp=> (he.and (h _ hp)).mono fun i hi=> hi.1.trans hi.2
lemma take (h:M.Rush p f)(ht:g=ᶠ[atTop] f): M.Rush p g:= h.view (ht.mono fun x hx=> by rw [hx])
lemma settle (v:ℝ) : M.Rush 0 (fun _=>v) := by
   intro p hp; exact (((tendsto_rpow_atTop hp).comp M.grows).eventually_ge_atTop _)
lemma zero : M.Rush d (0:ℕ→ℝ) := fun p hp=> M.eventual.mono fun i hi=>by unfold Meter.pow; simp only [Pi.zero_apply,norm_zero]; positivity
lemma any : M.Rush p (M.pow p):= fun q h=> (M.grows.eventually_ge_atTop 1).mono fun i hi=> (Real.norm_of_nonneg (Real.rpow_nonneg (zero_le_one.trans hi) _)).trans_le (Real.rpow_le_rpow_of_exponent_le hi h.le)
lemma times (h:M.Rush p f)(hr:M.Rush q g)(he:p+q=d): M.Rush d (fun i=>f i*g i):= by
   intro v hv; let e:=(v-d)/2; have hp:q+e>q:=by unfold e; linarith
   filter_upwards [h (p+e) (by linarith),hr _ hp,M.eventual] with i hi hf hM
   rw [norm_mul]; exact (mul_le_mul hi hf (norm_nonneg _) ((norm_nonneg _).trans hi)).trans_eq (by unfold Meter.pow; rw [← Real.rpow_add hM]; congr 1; unfold e; linarith only [he])
lemma multiplier (h:M.Rush p f)(v:ℝ): M.Rush p (fun i=>v*f i):= times (settle v) h (by ring)
lemma bind (h:M.Rush p f)(v:ℝ): M.Rush p (fun i=>f i*v):= times h (settle v) (add_zero _)
lemma blend (h:M.Rush p f)(he:M.Rush p g): M.Rush p (fun i=>f i+g i):= by
   intro q hq; let D:=(q-p)/2; have hv:0<D:= by unfold D; linarith
   filter_upwards [h (p+D) (by linarith),he (p+D) (by linarith),settle (M:=M) 2 D hv, M.eventual] with x hx he hv hh
   calc _ ≤ ‖f x‖+‖g x‖:= norm_add_le ..
        _ ≤ 2*M.pow (p+D) x:= (add_le_add hx he).trans_eq (two_mul _).symm
        _ ≤ (M.pow D x)*(M.pow (p+D) x):= mul_le_mul_of_nonneg_right (Real.norm_of_nonneg (by norm_num: (0:ℝ) ≤ 2) ▸ hv) (Real.rpow_nonneg hh.le _)
        _ = _ := by unfold Meter.pow; rw [← Real.rpow_add hh]; congr 1; unfold D; ring
lemma powers (h:M.Rush p f)(d:ℕ): M.Rush (p*d) (fun i=> f i^d):= by induction d with| zero=> simpa using (settle (M:=M) 1)|succ d ih=> simp_rw [pow_succ]; exact times ih h (by push_cast; ring)
end Rush
lemma rush_lax (h:M.Rush p f)(hp:p<q): ∀ᶠ i in atTop, ‖f i‖< M.pow q i:=by
   filter_upwards [(h ((p+q)/2) (by linarith)),M.grows.eventually_gt_atTop 1] with i hi hb; exact hi.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hb (by linarith))
lemma sliding (h:M.Rush p f)(hp:p<0)(x:ℝ)(hx:0<x): ∀ᶠ i in atTop, ‖f i‖<x:= by
   let φ:= -p/2; have hφ:0<φ:=by unfold φ; linarith
   filter_upwards [(h (-φ) (by unfold φ; linarith)), ((tendsto_rpow_neg_atTop hφ).comp M.grows).eventually_lt_const hx] with i hi hr using hi.trans_lt hr
-- Budget existence fax
structure Funds (M:Meter)(P:ℕ→ℝ→Prop)(p:ℝ): Prop where
    cap : ∃ f:ℕ→ℝ,M.Rush p f ∧ ∀ᶠ i in atTop, 0≤f i ∧ P i (f i)
namespace Funds
variable {X Y:ℕ→ℝ→Prop}
lemma lift (h:M.Funds P p)(hp: p≤q)(hq : ∀ᶠ i in atTop,∀ x:ℝ,0≤x→P i x→X i x): M.Funds X q:= by
   obtain ⟨f,hf,H⟩:= h.cap; exact ⟨f,hf.mono hp,(H.and hq).mono fun i hi=> ⟨hi.1.1,hi.2 _ hi.1.1 hi.1.2⟩⟩
lemma fold (h:M.Funds P p)(he:M.Funds X p)(hp:∀ᶠ i in atTop,∀ x y,0≤x→0≤y→P i x→X i y→Y i (x+y)): M.Funds Y p:= by
   obtain ⟨f,hf,H⟩:=h.cap; obtain ⟨g,hg,G⟩:=he.cap; exact ⟨_, hf.blend hg, (H.and (G.and hp)).mono fun i hi=>⟨add_nonneg hi.1.1 hi.2.1.1,hi.2.2 _ _ hi.1.1 hi.2.1.1 hi.1.2 hi.2.1.2⟩⟩
lemma meet (h:M.Funds P p)(he:∀ᶠ i in atTop, ∀ x y,0≤x→x≤y→P i x→P i y)(hp:p<q): ∀ᶠ i in atTop,P i (M.pow q i):= by
   obtain ⟨f,hf,H⟩:=h.cap; exact ( (hf q hp).and (H.and he)).mono fun i hi=> hi.2.2 _ _ hi.2.1.1 ((Real.norm_of_nonneg hi.2.1.1).symm.trans_le hi.1) hi.2.1.2
lemma loft (h:M.Funds P p)(ht:M.Rush q f)(hh : ∀ᶠ i in atTop, ∀ x,0≤x→P i x→X i (f i*x)) (hP : ∀ᶠ i in atTop,0≤f i)(he:p+q=d): M.Funds X d:= by
   obtain ⟨g,hg,H⟩:=h.cap; refine ⟨_,ht.times hg (by linarith),?_⟩; filter_upwards [H,hh,hP] with i hi h hp using ⟨mul_nonneg hp hi.1, h (g i) hi.1 hi.2⟩
end Funds
end Meter
end
end YM.Contacts.Loom
