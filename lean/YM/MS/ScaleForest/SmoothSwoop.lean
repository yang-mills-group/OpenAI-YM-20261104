import YM.MS.ScaleForest.VegSmooth
/-!
# weak continuity of dimensional/continuation-axis gluing

Both parameter-continuous (at fixed length with data varying continuously, or
moving length/generic parameters) operations for later position-domain and
interval integral. No inference from smooth costs alone. Require continuity
with costs in a neighborhood. This file: generic `swoop` statement on
such a neighborhood (topology can also be induced on it).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Function Filter Real Arc MeasureTheory Rock
open scoped Topology ContDiff
variable {I E F J:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
  [NormedAddCommGroup F][NormedSpace ℝ F] [NormedAddCommGroup J][NormedSpace ℝ J] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
variable [TopologicalSpace I] [FirstCountableTopology I]

abbrev hush (f:I→E→F) := ∀ x:E, Continuous (fun i=> f i x)

variable [MeasurableSpace F] [BorelSpace F] (μ:Measure F) [μ.IsAddHaarMeasure]

-- index-dependent factor c, normalized by 1. Integrate full Haar.
variable {f:I→F×E→ℂ}
omit [FiniteDimensional ℝ E] in
theorem hushHaar (hf : quiet 0 f 1) (he : hush f) (w:E) : Continuous (fun i=> ∫ x, f i (x,w) ∂μ) := by
   let N:= Module.finrank ℝ F+1; let D : F→ℝ := fun x=> ((1+‖x‖)^N)⁻¹
   obtain ⟨C,hC,k,hK⟩:= Q.man hf 0 N; let W:= C*(1+‖w‖)^k; have hw : 0 < W:= by unfold W; positivity
   simp only [norm_iteratedFDeriv_zero,Pi.zero_apply,Pi.one_apply,abs_zero,add_zero,mul_one,one_mul] at hK;
   have hD: Integrable D μ:= by convert Reserve.dustInteg (S:=Arc.path (0:UScale Unit)) (μ:=μ) () N (by unfold N; omega) using 1; ext; simp [Scale.dust, Scale.weight,D]
   refine continuous_of_dominated (fun i=> (hf.integrates (Reserve.cover N (by unfold N; omega)) i w).1) ?_ (hD.const_mul W) (Eventually.of_forall fun x=> he (x,w))
   intro i; refine Eventually.of_forall (fun x=>?_); unfold D; rw [← div_eq_mul_inv]; exact (le_div_iff₀ (by positivity)).mpr (hK i x w)
omit [FiniteDimensional ℝ E] in
theorem carpetHush {f:I→(F×ℝ)×E→ℂ} (hf : quiet 0 f 1) (he : hush f) : hush (fun i=> carpet μ (f i)):= fun p=> hushHaar μ (Q.trees hf) (fun q=> he ((q.1,q.2.1),q.2.2)) p
omit [FirstCountableTopology I] [FiniteDimensional ℝ E] in
theorem descent {f:I→ℝ×E→ℂ} (hf : quiet 0 f 1) (he : hush f) : hush (fun i=> Arc.d (f i)) := by intro p; exact plantAt (Q.common hf) he p (1,0)
omit [FirstCountableTopology I] [FiniteDimensional ℝ E] in
theorem chop_c {f:I→ ℝ×E→ℂ} (hf : quiet 0 f 1) (he : hush f) : hush (fun i=> chop (f i)) := by
   obtain hp := Q.common (Q.at_d (Q.at_d hf)); obtain h := continuousVeg hp (descent (Q.at_d hf) (descent hf he))
   intro x; apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ:=MeasureTheory.volume) (f:=fun i t=> Arc.d (Arc.d (f i)) (t*x.1,x.2)) (?_) 0 1
   exact h.comp (show Continuous (fun p:I×ℝ=> (p.1,(p.2*x.1,x.2))) by fun_prop)
omit [FirstCountableTopology I] [FiniteDimensional ℝ E] in
theorem prunedH {f:I→ ℝ×E→ℂ} (hf : quiet 0 f 1) (he : hush f) (hh:∀ i, Reflect (f i)) (m:ℕ) : hush (fun i=> pruning m (f i)):= by
   induction m with
   | zero=> exact he
   | succ n ih=> simp_rw [Arc.spent]; exact chop_c ((pruned hf hh n).1) ih

variable {f:I→ℝ×E→ℂ} {Z:I→ℂ} {N:ℕ}
   (hz : Continuous Z) (ht : ∀ i,Z i∈Town) (hv : ∀ i,2*(Z i).re+1≤ (N:ℝ))
include hz ht hv

-- an integrable envelope on μhalf (keep earlier norm weights if needed separately in proofs)
omit [FiniteDimensional ℝ E] in
theorem fetchedHush (hf : quiet 0 f 1) (he : hush f) : hush (fun i=> Arc.fetching (f i) (cloud (Z i))) := by
   intro x; let D : ℝ→ℝ:= fun p=> ((1+‖p‖)^2)⁻¹
   obtain ⟨C,hC,k,hK⟩:= Q.man hf 0 (N+2)
   have hD : Integrable D μhalf:= by
      have h : Integrable D MeasureTheory.volume:= by convert Reserve.dustInteg (S:=Arc.path (0:UScale Unit)) () 2 (by simp) (μ:=(MeasureTheory.volume : Measure ℝ)) using 1; ext p; simp [ Scale.dust, Scale.weight,D ]
      exact h.restrict -- separate
   simp only [norm_iteratedFDeriv_zero,Pi.one_apply,Pi.zero_apply,abs_zero,add_zero,one_mul,mul_one] at hK
   refine continuous_of_dominated (F:=fun i r=> cloud (Z i) r * f i (r,x)) ?_ ?_ (hD.const_mul (C*(1+‖x‖)^k)) ?_
   · exact fun i=> ((shade_major hf (shade_cloud ht hv) i).values x).1
   · intro i; filter_upwards [ show ∀ᵐ r : ℝ ∂μhalf, 0<r from ae_restrict_mem measurableSet_Ioi ] with r hr
     rw [norm_mul]; refine (mul_le_mul_of_nonneg_right (cloud_near (ht i) (hv i) hr) (norm_nonneg _)).trans ?_; unfold D; rw [← div_eq_mul_inv,le_div_iff₀ (by positivity)]; specialize hK i r x; rw [pow_add,← mul_assoc, mul_comm ‖f i _‖] at hK; exact hK
   filter_upwards [ show ∀ᵐ r : ℝ ∂μhalf, 0<r from ae_restrict_mem measurableSet_Ioi ] with r hr
   exact Continuous.mul (continuous_const.cpow (f:=fun _=> (r:ℂ)) (g:=fun i=> 2*Z i+1) (by fun_prop)
     (fun x=> Complex.ofReal_mem_slitPlane.mpr hr)) (he (r,x))

omit [FiniteDimensional ℝ E] in
theorem swoopH {f:I→(F×ℝ)×E→ℂ} (hf : quiet 0 f 1) (he : hush f) (hr : ∀ i, mirror (f i)) (m:ℕ) : hush (fun i=> swoop (Z i) μ m (f i)) := by
   have hp (i:I) : Reflect (carpet μ (f i)):= Arc.mirror_r μ (hr i)
   have hQ:= Arc.Q.Gquiet μ hf; intro p
   exact (fetchedHush hz ht hv (pruned hQ hp (m+1)).1 (prunedH hQ (carpetHush μ hf he) hp (m+1)) p).const_smul (gage m)
end YM.MS.ScaleForest
