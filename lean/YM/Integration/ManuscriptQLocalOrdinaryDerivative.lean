import YM.Integration.ManuscriptQLocalOrdinaryScale
import Mathlib.Analysis.Calculus.ParametricIntegral
import YM.Comparison.RG02.Cumulants.Partition

/-! Differentiate one actual finite conditional and its full normalized
connected array along the original ordinary-action line. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalOrdinaryDerivative

open Finset Filter MeasureTheory Wilson Lattice RG Comparison.RG02
open Marker Multi Extra.Trajectories Set
open scoped BigOperators Topology Classical

variable {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (e : α→ℝ) (z : α→ℂ)

def weighted (t : ℝ) (y : α) : ℂ := Real.exp ((1-t)*e y) • z y

def marked (t : ℝ) (y : α) : ℂ := (-e y) • weighted e z t y

def value (t : ℝ) : ℂ := ∫ y,weighted e z t y ∂μ
def score (t : ℝ) : ℂ := ∫ y,marked e z t y ∂μ

omit [MeasurableSpace α] in
theorem direction (t : ℝ) (y : α) :
    HasDerivAt (fun s=>weighted e z s y) (marked e z t y) t := by
  have h : HasDerivAt (fun s:ℝ=>(1-s)*e y) (-e y) t := by
    simpa using ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const (e y)
  have hx:=(Real.hasDerivAt_exp _).comp t h
  change HasDerivAt (fun s => Real.exp ((1-s)*e y) • z y)
    ((-e y) • (Real.exp ((1-t)*e y) • z y)) t
  rw [smul_smul, mul_comm (-e y) (Real.exp _)]
  exact hx.smul_const (z y)

omit [MeasurableSpace α] in
theorem multiplier {M : ℝ} (hM : ∀y,|e y|≤M) (t : ℝ) (y : α) :
    ‖weighted e z t y‖ ≤ Real.exp (|1-t| * M)*‖z y‖ := by
  have h : (1-t)*e y ≤ |1-t| * M := calc
    _ ≤ |(1-t)*e y| := le_abs_self _
    _ = |1-t| * |e y| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)
  simp only [weighted,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h) (norm_nonneg _)

theorem integrable (he : Envelope e) (hz : Integrable z μ) (t : ℝ) :
    Integrable (weighted e z t) μ := by
  obtain ⟨M,hM⟩:=he.cost
  apply (hz.norm.const_mul (Real.exp (|1-t| * M))).mono'
  · exact ((measurable_const.mul he.meas).exp.aestronglyMeasurable).smul hz.1
  · exact Eventually.of_forall (multiplier e z (fun y=>by simpa using hM y) t)

theorem differentiate (he : Envelope e) (hz : Integrable z μ) (t : ℝ) :
    HasDerivAt (value μ e z) (score μ e z t) t := by
  obtain ⟨M,hM⟩:=he.cost
  let C:=M*Real.exp ((|1-t|+1)*M)
  have hs y : |e y|≤M:=by simpa using hM y
  have bound (y : α) (s : ℝ) (h : s∈Metric.ball t 1) :
      ‖marked e z s y‖≤C*‖z y‖ := by
    have h₁ : 0 ≤ M := (abs_nonneg (e y)).trans (hs y)
    have h₂ := Metric.mem_ball.mp h
    have hr : |1-s|≤|1-t|+1 := calc
      |1 - s| = |(1-t)+(t-s)| := congrArg abs (by ring)
      _ ≤ |1-t| + |t-s| := abs_add_le _ _
      _ ≤ |1-t| + 1 := by
        have hts : |t-s| ≤ 1 := by simpa only [Real.dist_eq, abs_sub_comm] using h₂.le
        linarith only [hts]
    have hC : Real.exp (|1-s| * M)≤Real.exp ((|1-t|+1)*M) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr h₁)
    rw [marked,norm_smul,Real.norm_eq_abs,abs_neg]
    calc
      _ ≤ M * (Real.exp (|1-s| * M)*‖z y‖) :=
        mul_le_mul (hs y) (multiplier e z hs s y) (norm_nonneg _) h₁
      _ ≤ C*‖z y‖ := by dsimp [C]; rw [←mul_assoc];
                          gcongr
  have hb : Integrable (fun y=>C*‖z y‖) μ := hz.norm.const_mul C
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=weighted e z) (F':=marked e z) (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun s=>(integrable μ e z he hz s).1) (integrable μ e z he hz t)
    (he.meas.neg.aestronglyMeasurable.smul (integrable μ e z he hz t).1)
    (bound:=fun y=>C*‖z y‖) (Eventually.of_forall bound) hb
    (Eventually.of_forall fun y s _=>direction e z s y)).2

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}

/-- Each original mode has its own actual signed density and the same true quiet law. -/
def raw (f : Γ.Mode→α→ℂ) (t : ℝ) : Poly Γ := Poly.inject fun s=>value μ e (f s) t

def rate (f : Γ.Mode→α→ℂ) (s : Γ.Mode) (t : ℝ) : ℂ :=
  (score μ e (f s) t - (Order.unitScale (raw μ e f t)).part s *
    score μ e (f Γ.quiet) t) / value μ e (f Γ.quiet) t

omit [Fintype V] in
theorem normalized (he : Envelope e) (f : Γ.Mode→α→ℂ)
    (hf : ∀s,Integrable (f s) μ) (s : Γ.Mode) (t : ℝ)
    (h₀ : value μ e (f Γ.quiet) t≠0) :
    HasDerivAt (fun u=>(Order.unitScale (raw μ e f u)).part s) (rate μ e f s t) t := by
  have h:=(differentiate μ e (f s) he (hf s) t).div
    (differentiate μ e (f Γ.quiet) he (hf _) t) h₀
  have hfun : (fun u => (Order.unitScale (raw μ e f u)).part s) =
      value μ e (f s) / value μ e (f Γ.quiet) := by
    funext u
    change (value μ e (f Γ.quiet) u)⁻¹ * value μ e (f s) u =
      value μ e (f s) u / value μ e (f Γ.quiet) u
    rw [div_eq_mul_inv, mul_comm]
  have hrate : rate μ e f s t =
      (score μ e (f s) t * value μ e (f Γ.quiet) t -
        value μ e (f s) t * score μ e (f Γ.quiet) t) / value μ e (f Γ.quiet) t ^ 2 := by
    change (score μ e (f s) t - ((value μ e (f Γ.quiet) t)⁻¹ * value μ e (f s) t) *
      score μ e (f Γ.quiet) t) / value μ e (f Γ.quiet) t = _
    field_simp [h₀]
  rw [hfun, hrate]
  exact h

def linkedScore (f : Γ.Mode→α→ℂ) (s : Γ.Mode) (t : ℝ) : ℂ :=
  ∑h∈Multi.shards Γ s,Cumulants.mobiusTop h.val.card *
    ∑i∈h.val,rate μ e f i.val t *
      ∏j∈h.val.erase i,(Order.unitScale (raw μ e f t)).part j.val

private theorem derivPartitions {ι κ : Type*} [DecidableEq κ] (S : Finset ι) (parts : ι → Finset κ)
    (factor : ι → ℂ) (v : κ → ℝ → ℂ) (dv : κ → ℂ) (t : ℝ)
    (hv : ∀ i, HasDerivAt (v i) (dv i) t) :
    HasDerivAt (fun u => ∑ h ∈ S, factor h * ∏ j ∈ parts h, v j u)
      (∑ h ∈ S, factor h * ∑ i ∈ parts h, dv i * ∏ j ∈ (parts h).erase i, v j t) t := by
  have one (h : ι) := (HasDerivAt.finsetProd (u := parts h) (fun i _ => hv i)).const_mul (factor h)
  have all := HasDerivAt.fun_sum (fun h (_ : h ∈ S) => one h)
  simpa only [Finset.prod_apply, smul_eq_mul, mul_comm] using all

theorem linked (he : Envelope e) (f : Γ.Mode→α→ℂ)
    (hf : ∀s,Integrable (f s) μ) (s : Γ.Mode) (t : ℝ)
    (h₀ : value μ e (f Γ.quiet) t≠0) :
    HasDerivAt (fun u=>(connected (Order.unitScale (raw μ e f u))).part s)
      (linkedScore μ e f s t) t := by
  have hunit : ∀ᶠ u in 𝓝 t,(raw μ e f u).part Γ.quiet≠0 :=
    (differentiate μ e (f Γ.quiet) he (hf _) t).continuousAt.eventually_ne h₀
  have H := derivPartitions (Multi.shards Γ s) (fun h => h.val) (fun h => Cumulants.mobiusTop h.val.card)
    (fun i u => (Order.unitScale (raw μ e f u)).part i.val) (fun i => rate μ e f i.val t) t
    (fun i => normalized μ e he f hf i.val t h₀)
  exact H.congr_of_eventuallyEq (hunit.mono fun u hu => Cumulants.log_partition _ (Order.unitScore hu) s)

end YM.Integration.ManuscriptQLocalOrdinaryDerivative
end
