import YM.SchemeConversionRG11.FirstMS.DR.Bump
import YM.MSbar.Symbol.Azimuth
import YM.MSbar.Dim.Wide

/-!
# Dimensional position integration

Compact hats-rotational radial scalars. Radius argument t of `billAt` (not squared radius).
We'll not use angular averaging before MS CT extraction on ext hat tensors.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.SchemeConversionRG11.FirstMS.DR
open Function Set Filter MSbar MSbar.Dim MSbar.Symbol MeasureTheory Metric Complex
open scoped Topology ContDiff InnerProductSpace

-- s=extra dimension PAIRS, eps=-s.
def neighborhood : Set ℂ := ball 0 (1/8) -- keep one common analytic disk
lemma opened : IsOpen neighborhood := isOpen_ball
lemma occurs : (0:ℂ) ∈ neighborhood := mem_ball_self (by norm_num)

section Compact
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {u : Set ℂ} {f : ℂ × X → ℂ}

/-- Build AH from uniform compact support in real parameters. -/
theorem upon_packed (hu : IsOpen u) {K : Set X} (hK : IsCompact K)
    (he : ∀ z ∈ u, ∀ x ∉ K, f (z,x)=0)
    (hf : ∀ z : ℂ × X, z.1 ∈ u → ContDiffAt ℝ ∞ f z)
    (ht : ∀ z x, z ∈ u → DifferentiableAt ℂ (fun v ↦ f (v,x)) z) : AH u f :=
    AH.localized hu hf (fun z x hz=> ht z x hz) hK he
end Compact

abbrev Patch := E4 × ℝ
def billAt (s:ℂ) (f : Patch → ℂ) : ℂ := ∫ v:E4, Dim.radial (fun t => f (v,t)) s

section Bill
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable {F : ℂ×X×Patch → ℂ} {u : Set ℂ} {R : ℝ}

-- Fiber cut (|r| ≤ R and |v| ≤ R convenient closed square)
structure Window (u:Set ℂ) (R:ℝ) (F:ℂ×X×Patch → ℂ) : Prop where
  AH' : AH u F
  size : 0 ≤ R
  even : ∀ z ∈ u, ∀ x v, Function.Even fun t => F (z,x,v,t)
  ends : ∀ z ∈ u, ∀ x (p:Patch), R < ‖p‖ → F (z,x,p) = 0

variable (h: Window u R F) (hu:IsOpen u)
include h

lemma Window.radius (x:X) {z:ℂ} (hz:z∈u) (v:E4) : Radius R fun t ↦ F (z,x,v,t) :=
  ⟨h.size,(h.AH'.slice hz).1.comp (by fun_prop : ContDiff ℝ ∞ fun t:ℝ => (x,v,t)),h.even _ hz x v,
    fun t ht=> h.ends _ hz _ _ (ht.trans_le (le_trans (Real.le_norm_self _) (norm_snd_le (v,t))))⟩ -- lemma names

private lemma reorder : AH u (fun p:ℂ × ((X×E4) × ℝ) => F (p.1,p.2.1.1,p.2.1.2,p.2.2)) :=
   h.AH'.arguments ((ContinuousLinearEquiv.prodAssoc ℝ X E4 ℝ).hasTemperateGrowth)

include hu
private theorem socks : AH u (fun p:ℂ×(X×E4)=> radial (fun r=>F (p.1,p.2.1,p.2.2,r)) p.1) := by
   have hh : ∀ z∈u,∀ y : X × E4, Radius R fun t=>F (z,y.1,y.2,t):=fun _ hz y=> h.radius _ hz y.2
   have H := radial_AH (X:= X×E4) (t:=id) (F:=fun p : ℂ×((X×E4)×ℝ)=> F (p.1,p.2.1.1,p.2.1.2,p.2.2)) (U:=u) differentiableOn_id hu (reorder h) hh -- hil
   exact H

omit hu in
lemma Window.stops (x:X){z:ℂ}(hz:z∈u){v:E4}(hv : R < ‖v‖) : radial (fun r=> F (z,x,v,r)) z=0 := by
   rw [show (fun r:ℝ=> F (z,x,v,r)) = 0 from funext fun r=> h.ends _ hz x _ (hv.trans_le (norm_fst_le (v,r)))]
   exact emit_zero _

theorem Window.costs (x:X){z:ℂ}(hz:z∈u) : Integrable fun v => radial (fun r=> F (z,x,v,r)) z := by
   let g (v:E4) := radial (fun r => F (z,x,v,r)) z
   have hc : HasCompactSupport g := by
      refine (isCompact_closedBall (0:E4) R).of_isClosed_subset (isClosed_tsupport _) (closure_minimal (fun v hv=> ?_) isClosed_closedBall)
      apply mem_closedBall.mpr; rw [dist_zero_right]
      exact le_of_not_gt fun hv'=> hv (h.stops x hz hv')
   exact ((socks h hu|>.slice hz).1.continuous.comp (f:=fun t:E4=>(x,t)) (by fun_prop)).integrable_of_hasCompactSupport hc

theorem Window.integral : AH u (fun p:ℂ × X=> billAt p.1 (fun x=> F (p.1,p.2,x))) := by
   let K:= closedBall (0:E4) R
   have hc:IsCompact K:=isCompact_closedBall ..
   let μ:= volume.restrict K; haveI : IsFiniteMeasure μ:= ⟨by simpa only [μ,Measure.restrict_apply_univ] using (hc.measure_lt_top (μ:=volume))⟩
   refine ((socks h hu).after_average (p:=id) (μ:=μ) (integrable_const 1) aestronglyMeasurable_id (ae_restrict_mem (s:=K) hc.measurableSet) hc).congr hu fun z hz x=> ?_
   unfold billAt; simp only [one_mul, μ,id]
   exact setIntegral_eq_integral_of_forall_compl_eq_zero (s:=K) (fun v hv=> h.stops x hz (lt_of_not_ge (fun he=>hv (mem_closedBall.mpr (by simpa using he))))) -- check
omit hu in
lemma Window.zero (x:X) (hz:(0:ℂ)∈u) : billAt 0 (fun y=> F (0,x,y)) = ∫ v:E4,F (0,x,v,0) :=
   integral_congr_ae (Eventually.of_forall fun v => radial_zero (h.radius x hz v))

omit hu in
lemma Window.consts (x:X) {z:ℂ} (hz:z∈u) (c:ℂ) : billAt z (fun y=> c*F (z,x,y)) = c*billAt z (fun y => F (z,x,y)) := by
   unfold billAt; rw [← integral_const_mul]
   exact integral_congr_ae (Eventually.of_forall fun v=> radial_smul (h.radius x hz v) c z)

lemma Window.sum_bill {R' : ℝ} {G : ℂ × X × Patch → ℂ} (hG : Window u R' G) (x:X) {z:ℂ} (hz:z∈u):
   billAt z (fun y=>F (z,x,y)+G (z,x,y)) = billAt z (fun y=>F (z,x,y))+billAt z (fun y=>G (z,x,y)) := by
   unfold billAt; rw [← integral_add (h.costs hu x hz) (hG.costs hu x hz)]
   exact integral_congr_ae (Eventually.of_forall fun v=> radial_add (h.radius x hz v) (hG.radius x hz v) z)

end Bill
end YM.SchemeConversionRG11.FirstMS.DR
