import YM.AllOrder.Laplace.Star
import YM.X.Jet.Sparkle
import YM.PertExtension.PTBills
import Mathlib.Analysis.Analytic.IsolatedZeros
/-! Series convention. Real formal coupling powers (finite for every theorem),
matching PositionX solver normalization `someJ`. Powers same κ=t threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace.SigmaP
open PertExtension.Series Radial Tested Set Filter Function Asymptotics PositionX PositionX.Jet
open scoped Topology ENNReal ContDiff BigOperators Classical
variable {X:Type*}[NormedAddCommGroup X] [NormedSpace ℝ X] {n:ℕ}
variable {F G:ℝ→ℝ}{a b:ℕ→ℝ}
abbrev expS : Word ℝ → Word ℝ := run Real.exp
abbrev logS : Word ℝ → Word ℝ := run Real.log
abbrev plus := Tested.conv (𝕜:=ℝ)
lemma jet_entry {h:X→ℝ} (hs:ContDiffAt ℝ (↑n) h 0)(u:X): someJ (fun t:ℝ=>h (t•u)) n= jet h n u := by rw [homogeneous_derivative h u n hs]; rfl
lemma needed (h:ContDiffAt ℝ ω F 0): Aspiration F (someJ F) := by
   rw [show someJ F=(fun i=> jet F i 1) from funext fun i=> by simpa using jet_entry (h.of_le (show ↑i ≤ ω from le_top)) 1 ]; simpa only [smul_eq_mul,mul_one] using! directions (h.of_le le_top) 1
lemma some_mul (hf:ContDiffAt ℝ ω F 0)(hg:ContDiffAt ℝ ω G 0):someJ (F*G)=plus (someJ F) (someJ G):=(needed (hf.mul hg)).unique ((needed hf).prod (needed hg))
lemma exact_prod (h:Act n F a)(hg: Act n G b): Act n (F*G) (plus a b):= (eo_Act n (h.nice.mul hg.nice)).repairs fun i hi=> by change someJ (F*G) i = _; rw [some_mul h.nice hg.nice]; simp only [plus, Tested.conv, Tested.term,PowerSeries.coeff_mul,PowerSeries.coeff_mk]; refine Finset.sum_congr rfl fun j hj=>?_ ; have he:= Finset.mem_antidiagonal.mp hj; rw [h.writes _ (by omega),hg.writes _ (by omega)]
lemma exact_scale (x:ℝ) (a:Word ℝ): plus (just x) a=x • a := by funext i; let h:= Act.swell a (show i ≤ i from le_rfl); exact (exact_prod (Act.static x) h).trans_at (h.smul x) le_rfl
lemma some_add (hf:ContDiffAt ℝ ω F 0)(hg:ContDiffAt ℝ ω G 0):someJ (F+G)= someJ F+someJ G := funext fun i=> ((eo_Act i hf).add (eo_Act i hg)).writes i le_rfl
lemma exact_neg (hf:ContDiffAt ℝ ω F 0): someJ (-F)= -(someJ F):= by funext i; simpa only [Pi.smul_apply,neg_one_smul] using! ((eo_Act i hf).smul (-1)).writes i le_rfl
lemma some_sub (hf:ContDiffAt ℝ ω F 0)(hg:ContDiffAt ℝ ω G 0): someJ (F-G)=someJ F-someJ G:= by rw [sub_eq_add_neg,sub_eq_add_neg,some_add hf (show ContDiffAt ℝ ω (-G) 0 from hg.neg),exact_neg hg]
lemma conviction (hf:ContDiffAt ℝ ω F 0) : someJ (Real.exp ∘ F)= expS (someJ F):= funext fun i=> ((eo_Act i hf).transit (m:=Real.exp) Real.contDiff_exp.contDiffAt).writes i le_rfl
lemma log_read (hf:ContDiffAt ℝ ω F 0)(h:F 0≠0): someJ (Real.log ∘ F)= logS (someJ F):= funext fun i=> ((eo_Act i hf).transit (m:=Real.log) (by rw [someJ_zero]; exact Real.contDiffAt_log.mpr h)).writes i le_rfl
lemma log_mash (h:0<a 0)(hx:0<b 0): logS (plus a b)= logS a+logS b:= by
   funext i; have he:=Act.swell a (show i ≤ i from le_rfl); have hf:=Act.swell b (show i ≤ i from le_rfl)
   let f:=delay a i; let g:=delay b i; let A:= Real.log ∘ (f*g); let B:= (Real.log ∘ f)+(Real.log∘ g)
   have hy:f 0>0:= (h.trans_eq he.zero.symm); have hh:g 0>0:= (hx.trans_eq hf.zero.symm)
   have hi:0<plus a b 0:= by rw [← (exact_prod he hf).zero]; exact mul_pos hy hh
   have hb : A=ᶠ[𝓝 0] B:= by
      have hc:f 0∈Ioi 0:=hy; have hw:g 0∈Ioi 0:=hh
      filter_upwards [he.nice.continuousAt.eventually (isOpen_Ioi.mem_nhds hc),hf.nice.continuousAt.eventually (isOpen_Ioi.mem_nhds hw)] with x h H; exact Real.log_mul (show 0<f x from h).ne' (show 0<g x from H).ne'
   exact (Act.realizes (f:=A) hb ((exact_prod he hf).transit (m:=Real.log) (Real.contDiffAt_log.mpr hi.ne'))).trans_at ((he.transit (m:=Real.log) (Real.contDiffAt_log.mpr h.ne')).add (hf.transit (m:=Real.log) (Real.contDiffAt_log.mpr hx.ne'))) le_rfl
lemma log_expS (a:Word ℝ): logS (expS a)= a:= by
   funext i; have hf:=Act.swell a (show i ≤ i from le_rfl); have hx:=hf.transit (m:=Real.exp) Real.contDiff_exp.contDiffAt
   have hh:0<expS a 0 := by unfold expS; rw [← hx.zero]; exact Real.exp_pos _
   exact (hx.transit (Real.contDiffAt_log.mpr hh.ne')).trans_at (by simpa only [Function.comp_def, Real.log_exp] using hf) le_rfl
lemma log_const (c:ℝ)(hc:0<c): logS (just c)= just (Real.log c):= funext fun i=> ((Act.static (n:=i) c).transit (m:=Real.log) (Real.contDiffAt_log.mpr (show just c 0≠0 from hc.ne'))).trans_at (Act.static _) le_rfl
-- analytic division via fslope
variable [CompleteSpace X] {U:ℝ→X}
abbrev shift (U:ℝ→X) := dslope U 0
lemma shifty (h:ContDiffAt ℝ ω U 0):ContDiffAt ℝ ω (shift U) 0:= by
   obtain ⟨p,h⟩:=h.analyticAt; exact ((show AnalyticAt ℝ (shift U) 0 from ⟨_,h.has_fpower_series_dslope_fslope⟩).contDiffAt)
omit [CompleteSpace X] in
lemma shift_start (h:U 0=0)(t:ℝ): U t=t • shift U t := by simpa [h] using (sub_smul_dslope U 0 t).symm
lemma shift_down (h:F 0=0) (hf:ContDiffAt ℝ ω F 0): someJ (shift F)=fun i=>someJ F (1+i):= by
   have hm:=needed hf; have hA:=hm.shift (w:=1) (fun i hi=>by rw [show i=0 from (by omega),someJ_zero,h]); apply (needed (shifty hf)).unique; intro n; refine bill_match (EventuallyEq.sub ?_ (EventuallyEq.refl ..)) (hA n); exact Tested.eventually_pos.mono (fun i hi=> by dsimp; rw [pow_one]; nth_rw 1 [shift_start h i]; simp [smul_eq_mul, hi.ne']) -- edit
abbrev climb2 (U:ℝ→ℝ):= shift (shift U)
lemma shift_two (h:F 0=0)(hg:deriv F 0=0)(t:ℝ): F t=t^2* climb2 F t:= by
   have he:shift F 0=0:=by rw [shift,dslope_same]; exact hg
   nth_rw 1 [shift_start h t]; rw [shift_start he t,smul_eq_mul,smul_eq_mul,pow_two,mul_assoc] -- indentation
end YM.AllOrder.Laplace.SigmaP
