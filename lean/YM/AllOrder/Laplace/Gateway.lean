import YM.AllOrder.Laplace.Slice
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Laplace
open PertExtension.Series Radial Tested MeasureTheory Function Set Filter Metric
open scoped Topology ENNReal ContDiff Classical
variable {Y:Type} [NormedAddCommGroup Y][NormedSpace ℝ Y][FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y]
local notation "Ω" => ℝ×Y
variable {F K: ℝ×Y→ℝ}{a b:ℕ}
omit [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma equaljet {G:Ω→ℝ}(hF:F=ᶠ[𝓝 0] G) : jet F=jet G:=funext fun i=> funext fun x=>by rw [jet,jet,(hF.iteratedFDeriv ℝ i).eq_of_nhds]
omit [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] in
lemma Cylinder.changes {G L:Ω→ℝ}(h:Cylinder F K)(hF:F=ᶠ[𝓝 0] G)(hK:K=ᶠ[𝓝 0] L):Cylinder G L:= ⟨⟨h.revenue.smooth.congr_of_eventuallyEq hF.symm,hF.eq_of_nhds ▸ h.revenue.base0,(fun x=>equaljet hF ▸ h.revenue.base1 x)⟩,h.income.congr_of_eventuallyEq hK.symm, equaljet hF ▸ h.risen⟩
lemma outfits (hF:ContDiffAt ℝ ∞ F 0) : ∃ F':Ω→ℝ, F=ᶠ[𝓝 0] F' ∧ Measurable F' := by
  obtain ⟨s,hs,h₀,h⟩:= hF.contDiffOn' (m:=0) bot_le (by simp)
  simp only [insert_eq_of_mem (Set.mem_univ ..),univ_inter] at h
  obtain ⟨G,hG,h'⟩:= (MeasurableEmbedding.subtype_coe hs.measurableSet).exists_measurable_extend h.continuousOn.restrict.measurable fun _=>inferInstance
  exact ⟨G,(show ∀ᶠ y in 𝓝 0,y∈s from hs.mem_nhds h₀).mono (fun y hy=> (congr_fun h' ⟨y,hy⟩).symm),hG⟩ -- .eventually?
omit [FiniteDimensional ℝ Y][BorelSpace Y] in
lemma part_changes (μ:Measure Y) {G L:Ω→ℝ}(hF:F=ᶠ[𝓝 0] G)(hK:K=ᶠ[𝓝 0] L): part μ F K=part μ G L:=by
   funext i; have ht : layers F=layers G:= by funext u x; simp only [layers,equaljet hF]
   unfold part normTerm kernel integrandSeries; rw [equaljet hK,equaljet hF,ht]
omit [FiniteDimensional ℝ Y][MeasurableSpace Y][BorelSpace Y][NormedSpace ℝ Y] in
lemma round (p:Ω→Prop)(h:∀ᶠ x in 𝓝 0,p x):∀ᶠ δ in Tested.germ,∀ (t:ℝ), |t|≤δ→ ∀ (y:Y), ‖y‖≤δ → p (t,y):= by
 obtain ⟨d,hd,H⟩:= Metric.mem_nhds_iff.mp h
 filter_upwards [Tested.eventually_top hd] with δ ht
 intro t he y hy; exact H (mem_ball_zero_iff.mpr (show max ‖t‖ ‖y‖<d from (max_le he hy).trans_lt ht))
lemma stick_changes (μ:Measure Y) {G L:Ω→ℝ}(hF:F=ᶠ[𝓝 0] G)(hK:K=ᶠ[𝓝 0] L): ∀ᶠ δ in Tested.germ, stick μ F K δ=ᶠ[Tested.germ] stick μ G L δ:=by
   filter_upwards [round _ (hF.and hK),Tested.eventually_pos] with δ H hd
   filter_upwards [Tested.eventually_small hd] with t ht; apply setIntegral_congr_fun (disc_meas t δ) ; intro y hy; obtain ⟨he,hH⟩:= H t (abs_of_pos ht.1|>.symm ▸ ht.2.le) (t • y) (mem_ball_zero_iff.mp hy).le
   exact congr_arg₂ (fun i j=>i * Real.exp (-j/t^2)) hH he
lemma bill_match {n:ℕ}{f g:ℝ→ℝ} (h:f=ᶠ[Tested.germ] g)(h':Bill n f):Bill n g:=by
   obtain ⟨C,hC,H⟩:=h'; exact ⟨C,hC,(h.and H).mono fun i hi=> hi.1 ▸ hi.2⟩

-- eventually in collar order (allows path transport); not n-independent.
def Receipt (F:ℝ→ℝ→ℝ) (M : ℕ→ℝ) := ∀ n,∀ᶠ δ in Tested.germ,Bill (n+1) (F δ - peval M n)
lemma receipted (μ:Measure Y)[μ.HasTemperateGrowth] (h:Cylinder F K): Receipt (stick μ F K) (part μ F K):=by
   intro n; obtain ⟨G,hG,hm⟩:= outfits h.revenue.smooth; obtain ⟨L,hL,hK⟩:= outfits h.income; have hg:=h.changes hG hL
   rw [part_changes μ hG hL]; filter_upwards [arced μ hg n hm hK,stick_changes μ hG hL] with δ ht h; exact bill_match (h.symm.sub (EventuallyEq.refl _ _)) ht
lemma Receipt.add {f g:ℝ→ℝ→ℝ}{x y:ℕ→ℝ}(h:Receipt f x)(H:Receipt g y): Receipt (f+g) (x+y) := by
   intro n; filter_upwards [h n,H n] with δ h H; rw [show _-_=_ from (show (f+g) δ-peval (x+y) n=(f δ-peval x n)+(g δ-peval y n) from funext fun x=> by simp only [peval,Zone.eval,Pi.sub_apply,Pi.add_apply];simp only [smul_add,Finset.sum_add_distrib]; abel)]; exact bill_add h H
lemma Receipt.smul {f:ℝ→ℝ→ℝ}{x:ℕ→ℝ}(h:Receipt f x) (c:ℝ):Receipt (c • f) (c • x):= by
   intro n; filter_upwards [h n] with δ h; obtain ⟨C,hC,H⟩:=h; refine ⟨|c| * C,by positivity,?_⟩ ; filter_upwards [H] with z Hz
   rw [show _-_=_ from (show (c • f) δ-peval (c • x) n=c • (f δ-peval x n) from funext fun y=> by simp only [peval,Zone.eval,Pi.smul_apply,Pi.sub_apply]; rw [smul_sub, Finset.smul_sum]; congr 1; exact Finset.sum_congr rfl fun j _=> smul_comm ..  )] -- fix
   rw [Pi.smul_apply,norm_smul,Real.norm_eq_abs,mul_assoc];gcongr
lemma Receipt.moved {f g:ℝ→ℝ→ℝ}{x:ℕ→ℝ}(h:Receipt f x)(hg:∀ᶠ δ in Tested.germ, f δ=ᶠ[Tested.germ] g δ):Receipt g x:= fun n=> (hg.and (h n)).mono fun _ hi=>bill_match (hi.1.sub (EventuallyEq.refl ..)) hi.2
end YM.AllOrder.Laplace
