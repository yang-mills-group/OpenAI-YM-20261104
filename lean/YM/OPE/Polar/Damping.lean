import YM.OPE.Polar.Reflect
/-!
# Real direction budget on a penalized high ball
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Polar
open Function Set Filter Metric Complex
open scoped Topology BigOperators
variable {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]
variable {f:X→ℂ}{N B K:ℝ}

structure Radiates (f:X→ℂ)(x v:X)(B:ℝ) : Prop where
    holds : ∃ F:ℂ→ℂ,(∀ z∈closedBall (0:ℂ) 1, DifferentiableAt ℂ F z)∧ (∀ s:ℝ,|s|≤1→F (s:ℂ)=f (x+s • v)) ∧ ∀ z∈closedBall (0:ℂ) 1, ‖F z‖ ≤ B

variable {x y v:X}
lemma Radiates.mono (h:Radiates f x v B)(hx:B≤K): Radiates f x v K:= by obtain ⟨F,d,e,z⟩:=h.holds; exact ⟨F,d,e,fun z' hz=> (z z' hz).trans hx⟩
lemma Radiates.at_center (h:Radiates f x v B): ‖f x‖ ≤ B:= by
    obtain ⟨F,-,hA,hF⟩:= h.holds; have hf:= hF 0 (mem_closedBall_self zero_le_one); rwa [show F 0=f x from (by simpa using hA 0 (by simp))] at hf
lemma Radiates.zero (h:‖f x‖ ≤ B): Radiates f x 0 B:=
    ⟨fun _=> f x, fun _ _=>differentiableAt_const _,fun _ _=>by simp, fun _ _=>h⟩
lemma Radiates.smul (t:ℂ) (h: Radiates f x v B): Radiates (fun y=> t*f y) x v (‖t‖*B):= by obtain ⟨F,h,e,hZ⟩:= h.holds; exact ⟨fun y=>t*F y,fun z hz=>(differentiableAt_const t).mul (h z hz),fun y hy=>by simp only [e y hy],fun z hz=> by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hZ z hz) (norm_nonneg t)⟩
lemma Radiates.smulReal (t:ℝ) (h:Radiates f x v B): Radiates (fun y=> t • f y) x v (‖t‖*B):= by simp_rw [Complex.real_smul]; have he:=h.smul (t:ℂ); simpa only [Complex.norm_real] using he
lemma Radiates.add {g:X→ℂ}(h:Radiates f x v B)(hg: Radiates g x v K): Radiates (fun x=>f x+g x) x v (B+K):=by obtain ⟨F,h,e,hF⟩:=h.holds; obtain ⟨G,hg,e',hG⟩:=hg.holds; exact ⟨fun z=>F z+G z,fun z hz=>(h z hz).add (hg z hz),fun y hy=>by simp only [e y hy,e' y hy],fun z hz=> (norm_add_le ..).trans (add_le_add (hF z hz) (hG z hz))⟩
lemma Radiates.norm_sens (h:Radiates f x v (Real.exp N)) (hh:DifferentiableAt ℝ f x) (hn:1 ≤ N)(ha:1 ≤ B)(hx:∀ s:ℝ, |s|≤1 → ‖f (x+s • v)‖ ≤ B) : ‖fderiv ℝ f x v‖ ≤ Real.exp 4*B*N:=by
    obtain ⟨F,h,e,hF⟩:= h.holds; have ht:= budget hn h (fun z hz=>hF z (mem_closedBall_zero_iff.mpr hz)) (fun y hy=>by rw [e y hy]; exact hx y hy) ha; let g:= fun t:ℝ=> x+t • v
    have hH : HasDerivAt g v (0:ℝ):=by
       simpa only [one_smul] using (((hasDerivAt_id' (x:=(0:ℝ))).smul_const v).const_add x)
    have hf : HasDerivAt (f ∘ g) ((fderiv ℝ f x) v) 0:=by
       have he:g 0=x:=(by simp [g]); exact (((show DifferentiableAt ℝ f (g 0) from he.symm ▸ hh).hasFDerivAt).comp_hasDerivAt 0 hH) |>.congr_deriv (by rw [he]) -- name
    have he: HasDerivAt (f ∘ g) (deriv F 0) 0:=by
       have hv: HasDerivAt F (deriv F 0) (↑(0:ℝ):ℂ):= by rw [ofReal_zero]; exact (h 0 (mem_closedBall_self zero_le_one)).hasDerivAt
       refine hv.comp_ofReal.congr_of_eventuallyEq ?_; filter_upwards [ge_mem_nhds zero_lt_one,le_mem_nhds (by norm_num : (-1:ℝ) < 0)] with i hi hh using (e i (abs_le.mpr ⟨hh,hi⟩)).symm
    rw [hf.unique he]; exact ht
lemma Radiates.contract (h:Radiates f x v B) {a:ℝ}(hp: |a| ≤ 1) : Radiates f x (a • v) B:=by
    obtain ⟨F,d,e,hF⟩:= h.holds; have hx (z:ℂ)(hz:z∈ closedBall (0:ℂ) 1): z*a ∈ closedBall (0:ℂ) 1:=by rw [mem_closedBall_zero_iff,norm_mul,Complex.norm_real]; exact (mul_le_of_le_one_right (norm_nonneg _) hp).trans (mem_closedBall_zero_iff.mp hz)
    refine ⟨fun z=>F (z*a), fun z hz=>(d _ (hx z hz)).comp (f:=fun z:ℂ=>z*a) z (by fun_prop),fun y hy=>?_,fun z hz=>hF _ (hx z hz)⟩
    dsimp only; rw [← Complex.ofReal_mul,smul_smul]; exact e _ (by rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) hp).trans hy)
structure Watches (f:X→ℂ)(x:X)(N K:ℝ) : Prop where
    origin : ‖f x‖ ≤ Real.exp N
    analyticAxes : ∀ F : X →L[ℝ] ℂ, ∀ A≥0, (∀ v:X, ‖v‖≤1 → Radiates f x v (Real.exp N) → ‖F v‖≤ A) → ‖F‖≤ K*A
    good : DifferentiableAt ℝ f x
lemma Watches.raise (h: Watches f x N K){q r:ℝ}(hp:N≤q)(hx:K≤r):Watches f x q r:=by
    have hf:=Real.exp_monotone hp; exact ⟨h.origin.trans hf,fun F A hA he=> (h.analyticAxes F A hA (fun v hz hd=> he v hz (hd.mono hf))).trans (mul_le_mul_of_nonneg_right hx hA),h.good⟩
lemma Watches.paid (h: Watches f x N K)(hn:1 ≤ N)(hh:1≤B)(hz:∀ y∈ closedBall x (4*N)⁻¹, ‖f y‖ ≤ B):
    ‖fderiv ℝ f x‖ ≤ K*(4* Real.exp 4*B*N^2):=by
    have hn':0<N:= zero_lt_one.trans_le hn; have ht:0<4*N:=(by positivity); let y:=(4*N)⁻¹; have hy: y ≤ 1:= inv_le_one_of_one_le₀ (by linarith)
    have hy': 0 < y:= inv_pos.mpr ht; apply h.analyticAxes _ _ (by have he:=zero_lt_one.trans_le hh; positivity); intro v hv hd
    have hx:= (hd.contract (show |y|≤1 by rwa [abs_of_nonneg hy'.le])).norm_sens h.good hn hh (fun z he=> hz _ (mem_closedBall.mpr (by rw [dist_eq_norm,add_sub_cancel_left, norm_smul,norm_smul,Real.norm_of_nonneg hy'.le]; exact (mul_le_of_le_one_left (mul_nonneg hy'.le (norm_nonneg _)) he).trans (mul_le_of_le_one_right hy'.le hv))))
    rw [map_smul,norm_smul,Real.norm_of_nonneg hy'.le] at hx; apply (mul_le_mul_iff_right₀ hy').1; apply hx.trans; unfold y; field_simp; linarith only -- notation lemma likely left
end YM.OPE.Polar
