import YM.AllOrder.Laplace.Price
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested Set Metric Filter Function PositionX.Jet
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {Y X:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y] [NormedAddCommGroup X][NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {F K:X→ℝ}
lemma ascend (G:X→ℝ) (x:X) (h: ContDiffAt ℝ ω G 0): ContDiffAt ℝ ω (fun s:ℝ=> G (s • x)) 0 := (show ContDiffAt ℝ ω G ((0:ℝ) • x) from (by rw [zero_smul]; exact h)).comp (f:=fun t:ℝ=> t • x) _ (contDiffAt_id.smul contDiffAt_const)
omit [FiniteDimensional ℝ X] in
lemma advance (x:X) (h:HasFDerivAt (𝕜:=ℝ) F 0 0): deriv (fun s:ℝ=> F (s•x)) 0=0 := by
   have hx:HasFDerivAt (𝕜:=ℝ) F 0 ((fun r:ℝ=>r • x) 0):= by rwa [show (fun r:ℝ=>r • x) 0=0 by simp];
   exact (hx.comp_hasDerivAt 0 ((hasDerivAt_id' (0:ℝ)).smul_const x)).deriv -- order
/-- Repriced at analytic shifts; using any tame path H. -/
lemma coined {g:ℝ→ℝ}(H:Radial.Stationary F)(hk:ContDiffAt ℝ ∞ K 0)(hg:ContDiffAt ℝ ω g 0)(x:X) (h: ∀ᶠ s in Tested.germ, projection K F s x=g s) : (fun n=> normTerm K F n x)=someJ g:= by
 have he:= integrand hk H (zero_lt_one)
 refine Aspiration.unique (f:=g) ?_ (needed hg); intro n
 obtain ⟨δ,C,e,hδ,hC,h'⟩:= (he.fits n).cost; let Z:=Radial.zone (E:=X); let r:= Radial.shade 1 x; let a:= kernel F x
 have hP:0≤r:= (Real.exp_pos _).le; have hA:0≤a:= (Real.exp_pos _).le; let D:= Z.w x; have hD:0<D:= zero_lt_one.trans_le (Z.high x)
 refine ⟨(C*D^e*r)*a,by positivity,?_⟩; filter_upwards [Tested.eventually_small (show 0<δ/D from div_pos hδ hD),h] with t ht hf
 change ‖g t- _‖ ≤_ ; rw [← hf]
 unfold projection; let f:=Zone.eval (integrandSeries F K) n t x; have hy : ‖insertion F K t x - f‖ ≤ C*D^e*r*t^(n+1):= h' x t ht.1 ((lt_div_iff₀ hD).mp ht.2).le
 rw [show peval (fun n=> normTerm K F n x) n t = f*a by unfold peval Zone.eval f normTerm; unfold Zone.eval; simp only [Finset.sum_mul,smul_eq_mul,mul_assoc]; rfl]
 rw [show kernel F x=a from rfl, ← sub_mul, norm_mul,Real.norm_of_nonneg hA]; exact (mul_le_mul_of_nonneg_right hy hA).trans_eq (by ring)

lemma retrace {h:ℝ→ℝ}(hf:h 0=0)(hv:deriv h 0=0)(hT:ContDiffAt ℝ ω h 0): someJ (climb2 h)=fun i=>someJ h (i+2):= by
 unfold climb2; rw [shift_down (show shift h 0=0 from (by rw [shift,dslope_same]; exact hv)) (shifty hT), shift_down hf hT]; funext i; dsimp only; rw [show 1+(1+i)=i+2 from (by omega)]
-- canonical radial shift coefficient
lemma sharp (F:X→ℝ)(x:X)(hf:ContDiffAt ℝ ω F 0)(h:F 0=0)(he:fderiv ℝ F 0=0): someJ (climb2 (fun t:ℝ=>F (t•x)))=fun i=>jet F (i+2) x:= by
 rw [retrace (show F ((0:ℝ)• x)=0 from (by simpa [h])) (advance x (he ▸ (hf.differentiableAt (by simp)).hasFDerivAt)) (ascend F x hf)]
 exact funext fun i=> jet_entry (hf.of_le le_top) _
end YM.AllOrder.Laplace.SigmaP
