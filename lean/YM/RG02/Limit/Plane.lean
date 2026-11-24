import YM.RG02.Limit.Ball

/-!
# Parameter carried with the integration variable

Frozen parameter-ray direction, integrate only over slice fields. Keep
Borel and growth in full finite space. `pin` equivalent to Dirac 1 × covolume.
No tilting of that measure by marker names; deterministic changes with coarse
BACKGROUND and tails estimated elsewhere. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG02.Therm
open Filter Function MeasureTheory Set Metric
open PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Asym
open PowerSeries
open scoped ContDiff Topology Classical Real
variable {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]

def post (E : Type) : E → ℝ×E:=fun v => (1,v)
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma station : MeasurableEmbedding (post E)  := by
   refine ⟨fun i j H => congr_arg Prod.snd H, measurable_const.prodMk measurable_id,?_⟩
   intro s hs; rw [show post E '' s={(1:ℝ)} ×ˢ s by ext ⟨a,b⟩;simp [post, eq_comm,and_comm]]; exact (measurableSet_singleton _).prod hs

variable (μ : Measure E)

def pin := Measure.map (post E) μ
instance [μ.HasTemperateGrowth] : (pin μ).HasTemperateGrowth := by
   obtain ⟨u,H⟩ := Measure.HasTemperateGrowth.exists_integrable (μ:=μ)
   let p : ℝ := -(u:ℝ)
   let f := fun x: ℝ×E => (1+‖x‖)^p
   refine ⟨u, ?_⟩
   change Integrable f (Measure.map (post E) μ)
   rw [(station (E:=E)).integrable_map_iff]
   refine H.mono' ((show Measurable (f ∘ post E) by unfold f post; fun_prop).aestronglyMeasurable) ?_
   apply ae_of_all; intro x
   change ‖(1+‖post E x‖)^p‖ ≤ _
   rw [Real.norm_eq_abs,abs_of_nonneg (a:=(1+‖_‖)^p) (by positivity)];
   apply Real.rpow_le_rpow_of_nonpos
   · positivity
   · gcongr; exact norm_snd_le (post E x)
   exact neg_nonpos.mpr (Nat.cast_nonneg _)

def turbine (f:ℝ× E→ℝ)(t:ℝ)(u:E):= Real.exp (-f (t,t • u)/t^2)
def sheet (f:ℝ × E→ℝ)(K:ℝ × E→ℂ)(t:ℝ)(u:E) := K (t,t • u) * ↑(turbine f t u)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma recover_sheet (f:ℝ× E→ℝ)(K:ℝ× E→ℂ)(t:ℝ) : (beam K f t ∘ post E) = sheet f K t := by
   funext u; simp only [sheet,turbine,post,beam,comp_apply,Prod.smul_mk,smul_eq_mul,mul_one]

private lemma slices {r t : ℝ}(ht : 0<t)(S : Set E) (hT : t<r)(hS : S⊆ disc t r) :
    let A : Set (ℝ×E):= (Prod.snd ⁻¹' S) ∩ disc t r
    (post E) ⁻¹' A=S := by
   intro A
   ext u
   constructor
   · intro h; exact h.1
   intro hu
   refine ⟨hu,(disc_mem ht.le r _).2 ?_⟩
   rw [Prod.norm_def, mul_max_of_nonneg _ _ ht.le];
   exact max_lt (by simp [post,hT]) ((disc_mem ht.le _ u).1 (hS hu))

variable [μ.HasTemperateGrowth]
lemma fly {f:ℝ× E→ℝ}(H : Stationary f)(hg : ∃ c>0,∀ u:ℝ× E,c*‖u‖^2≤jet f 2 u)
    (hf : Measurable f){K:ℝ× E→ℂ}(hk : ContDiffAt ℝ ∞ K 0)(hm : Measurable K) :
    ∃ r>0,∀ S : ℝ→Set E, Collars r S → (∀ n, Integrable (visibly f K n ∘ post E) μ) ∧
      (∀ᶠ t in Tested.germ, IntegrableOn (sheet f K t) (S t) μ) ∧
      Near (fun t=>∫ u in S t, sheet f K t u ∂μ) (PowerSeries.mk fun n=>∫ u, visibly f K n (1,u) ∂μ) := by
   obtain ⟨r,hr,H⟩ := traction (pin μ) H hg hf hk hm
   let e := station (E:=E)
   refine ⟨r,hr,fun S hS =>?_⟩
   let A := fun t=> (Prod.snd ⁻¹' S t) ∩ (disc t r : Set (ℝ× E))
   obtain ⟨b,hb,hb',HB⟩ := hS
   have he : Collars r A := by
      refine ⟨b,hb,hb',?_⟩
      filter_upwards [Tested.eventually_pos,HB] with t ht hT
      refine ⟨(measurable_snd hT.1).inter (disc_meas ..),?_,inter_subset_right⟩
      intro x hx; refine ⟨hT.2.1 ((disc_mem ht.le _ _).2 (lt_of_le_of_lt ?_ ((disc_mem ht.le _ x).1 hx))),ball_subset_ball hb' hx⟩
      exact mul_le_mul_of_nonneg_left (norm_snd_le x) ht.le
   obtain ⟨hh,h,hA⟩ := H A he
   have ha (t : ℝ) (ht : 0<t) (hv : t<r)(hw : S t⊆disc t r) :
        (pin μ).restrict (A t) = Measure.map (post E) (μ.restrict (S t)) := by
        unfold pin; rw [e.restrict_map]; rw [show _ = S t from slices ht (S t) hv hw]
   have hg := (Tested.eventually_small hr).and HB
   refine ⟨fun n => e.integrable_map_iff.mp (hh n),?_,?_⟩
   · filter_upwards [h,hg] with t Ht ht
     unfold IntegrableOn at Ht ⊢; rw [ha t ht.1.1 ht.1.2 ht.2.2.2,e.integrable_map_iff, recover_sheet] at Ht
     exact Ht
   have HU := fun n : ℕ => show ∫ u, visibly f K n u ∂pin μ=∫ u:E, visibly f K n (1,u) ∂μ from e.integral_map _
   simp_rw [HU] at hA; apply Near.same hA
   filter_upwards [hg] with t ht
   rw [ha t ht.1.1 ht.1.2 ht.2.2.2,e.integral_map, ← recover_sheet]; rfl
end YM.RG02.Therm
