import YM.OPE.Compatible.Sear.Dine
/-! # Secular ages and negligible omitted cells of gaussian -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {I:Type*}{s t c:ℝ}{i j k:ℕ}{T:I→ℝ}{l:Filter I}
open PertExtension Series Libra GaussianScore Jargon
variable {X:I→ Type*}{Yz:I→Type*}[∀ i,MeasurableSpace (X i)]{μ:∀ i,Measure (X i)} [∀ i, IsProbabilityMeasure (μ i)]
variable {p q:PayR X} {S:∀ i, Set (X i)}
lemma indicatorX (S:∀ i, Set (X i))(hg:∀ᶠ i in l,MeasurableSet (S i))(hp:∀ q:ℝ, RateLE l T (fun i=> (μ i).real (S i)) q)(he:Tendsto T l atTop) (s:ℝ): Grain μ l T (fun i=> (S i).indicator (fun _=>1)) s:=by
       intro j hj; let f(i):= Real.exp (s*T i); refine ⟨f,?_,?_⟩
       · intro x hx; filter_upwards [he.eventually_ge_atTop 0] with i hu; rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; apply Real.exp_monotone; gcongr
       filter_upwards [hp (j*s-1) (j*s) (by linarith),hg] with i hΦ hP; let r:= (S i).indicator (fun _=>1: X i→ℝ); apply Fault.ofInt (Real.exp_nonneg _) hj (aestronglyMeasurable_const.indicator hP)
       · refine Integrable.congr ((integrable_const 1 (μ:=μ i)).indicator hP) ?_; filter_upwards with x; change r x= ‖r x‖^j; unfold r; by_cases h:x∈S i
         · rw [indicator_of_mem h,norm_one,one_pow]
         rw [indicator_of_notMem h,norm_zero,zero_pow hj.ne']
       rw [show (fun x=>‖r x‖^j)=r from ?_]; rw [show (∫ x,r x ∂μ i)=(μ i).real (S i) from (integral_indicator hP).trans (by rw [setIntegral_const,smul_eq_mul,mul_one])]; rw [←Real.exp_nat_mul, ← mul_assoc]; exact (Real.le_norm_self _).trans hΦ
       funext x; unfold r; by_cases h:x∈S i; · rw [indicator_of_mem h,norm_one,one_pow];
       rw[indicator_of_notMem h,norm_zero,zero_pow hj.ne']
lemma missingI (p:PayR X)(S:∀ i, Set (X i))(hg:∀ᶠ i in l,MeasurableSet (S i))(hp:∀ q:ℝ, RateLE l T (fun i=> (μ i).real (S i)ᶜ) q)(he:Tendsto T l atTop)(h:Grain μ l T p t)(s:ℝ): RateLE l T (fun i=>(∫ x in S i,p i x ∂μ i) -(∫ x,p i x ∂μ i)) s:=by
        let f(i):= (S i)ᶜ.indicator (p i)
        have hv : Grain μ l T f s:=by
             let g:= indicatorX (μ:=μ) (fun i=> (S i)ᶜ) (hg.mono fun _ hi=>hi.compl) hp he (s-t); apply Grain.shift ((g.mul h).mint (le_of_eq (sub_add_cancel ..))); filter_upwards with i; unfold f; funext x; by_cases h:x∈(S i)ᶜ<;>simp only[indicator_of_mem,indicator_of_notMem,h,not_false_eq_true,one_mul,zero_mul]
        refine RateLE.congr (hv.integral.2.neg) ?_; filter_upwards [hg,h.integral.1] with i hT hφ; rw [← integral_add_compl hT hφ]; unfold f; rw[integral_indicator hT.compl]; ring -- anchor
-- supremum agreement in domain; no ℝ≤0 α here
omit [∀ i,MeasurableSpace (X i)][∀ i,IsProbabilityMeasure (μ i)] in
def Large {Y:I→Type*}[∀ i,Norm (Y i)] (S:∀ i, Set (X i))(l:Filter I)(T:I→ℝ)(p:(i:I)→ X i→ Y i)(t:ℝ): Prop:=∃ f:I→ℝ,RateLE l T f t ∧ ∀ᶠ i in l,∀ x∈S i, ‖p i x‖≤ ‖f i‖
section
omit [∀ i,MeasurableSpace (X i)][∀ i,IsProbabilityMeasure (μ i)]
namespace Large
lemma fromR (p:I→ℝ)(h:RateLE l T p s): Large S l T (fun i _=>p i) s:= ⟨p,h,Eventually.of_forall fun _ _ _=>le_rfl⟩
lemma hMono (h:Large S l T p s)(he:∀ᶠ i in l,∀ x∈S i,‖q i x‖ ≤ ‖p i x‖): Large S l T q s:=by obtain ⟨z,hz,H⟩:=h; exact ⟨z,hz,(H.and he).mono fun i hi=> fun x hx=>(hi.2 x hx).trans (hi.1 x hx)⟩
lemma grow (h:Large S l T p s)(he:s ≤ t):Large S l T p t:=by obtain ⟨z,hz,H⟩:=h;exact ⟨z,hz.mono he,H⟩
lemma added (h:Large S l T p s)(hp:Large S l T q s)(hL:Tendsto T l atTop):Large S l T (p+q) s:=by
       obtain ⟨w,hw,h⟩:=h; obtain ⟨x,hx,hp⟩:=hp; refine ⟨_,hw.norm.add hx.norm hL,(h.and hp).mono fun i h y he=>?_⟩;exact (norm_add_le ..).trans ((add_le_add (h.1 y he) (h.2 y he)).trans (Real.le_norm_self _))
lemma subed (h:Large S l T p s)(hp:Large S l T q s)(hL:Tendsto T l atTop):Large S l T (p-q) s:=by rw [sub_eq_add_neg]; apply h.added (hp.hMono _) hL; filter_upwards with i x hx; rw[Pi.neg_apply,Pi.neg_apply,norm_neg]
lemma times (h:Large S l T p s)(he:Large S l T q t):Large S l T (p*q) (s+t):=by
       obtain ⟨x,hx,h⟩:=h;obtain ⟨y,hy,hp⟩:=he;refine ⟨_,hx.mul hy,(h.and hp).mono fun i h v hv=>?_⟩;simp only[Pi.mul_apply,norm_mul];exact mul_le_mul (h.1 v hv) (h.2 v hv) (norm_nonneg _) (norm_nonneg _)
end Large
end
namespace Large
lemma crop (_hI:∀ᶠ i in l, MeasurableSet (S i))(h:Large S l T p s)(hg:∀ᶠ i in l, AEStronglyMeasurable ((S i).indicator (p i)) (μ i)): Grain μ l T (fun i=>(S i).indicator (p i)) s:=by
       intro k hk; obtain ⟨x,hx,H⟩:=h; refine ⟨_,hx.norm,(H.and hg).mono fun i hi=>?_⟩; refine Fault.bound (norm_nonneg _) hi.2 (ae_of_all _ fun v=>?_); change ‖(S i).indicator (p i) v‖ ≤ _; by_cases h:v∈S i; · rw[indicator_of_mem h]; exact hi.1 v h
       rw [indicator_of_notMem h,norm_zero]; exact norm_nonneg _
end Large
end YM.OPE.Cinders
