import YM.SchemeConversionRG11.FirstW.Hart.Fountain
/-! Exterior polynomial packet with data convergence. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set Metric Lattice Pert Align Maxwell Topology
open scoped BigOperators Classical
variable {T : Itinerary} {G : Gauge} {n : Side} {R : ℝ}
lemma arrived (k : Labels.Key G) (x : StepPath T) {v:E4} (hx : sails T x v) (a : Axis) : Score T {u:E4|u≠v} (fun i y=>(T.gap i)⁻¹ • river (T.gap i) k (x i) (y,a)) (fun D u=> tongs k a D (u-v)) := by
  have H := Score.resite (stream k T a) (-x) (sails_neg hx) {u:E4|u≠v} (fun u hu=> (show u+-v≠0 by rw [←sub_eq_add_neg]; exact sub_ne_zero.mpr hu))
  have he (i:ℕ) y : river (T.gap i) k (x i) (y,a) = river (T.gap i) k (0:Site (T.period i)) (y+(-x) i, a) := by
    simp only [river,Pi.smul_apply]; rw [carried (o:=x i), sub_eq_add_neg];rfl
  simp_rw [he, sub_eq_add_neg]; exact H
lemma arrived_poly (k : Labels.Key G) (x : StepPath T) {v:E4} (hv:sails T x v) (hR : 0 < R) (hp : 2*R < ‖v‖) (m : ℕ) : ∃ α:Age G, (∀ i≤m,Book (α i)) ∧ Messed T R m (fun i=> terms (0:Site (T.period i)) (river (T.gap i) k (x i))-composeR T m α i) := by
  let f i:= terms (0:Site (T.period i)) (river (T.gap i) k (x i));
  have hc : Metric.closedBall (0:E4) (2*R) ⊆ {u| u≠v} := fun u hu h=> hp.not_ge (by subst u; simpa using hu)
  have he:=bound_order (T:=T) (fun i=> river (T.gap i) k (x i)) f hR (fun a=> Score.restrict hc (arrived k x hv a)) (fun _=>rfl) m
  obtain ⟨Y,hs,Hp⟩:= tuning f he.1 hR (detectors_echo k x hv (norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by linarith only [hR]) hp)))) -- norm syntax
  obtain ⟨α,hα,H⟩:=luminosity T m Y (tunedMon f Hp he.2)
  simp_rw [H] at hs; exact ⟨α,hα,hs⟩
end YM.RG11.FirstW
