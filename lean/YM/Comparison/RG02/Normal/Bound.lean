import YM.Comparison.RG02.Actual.Mask
import YM.Push.BETA_TRANSPORT.Block
/-!
# Denominator and tagged (tilted) probability

This is on the same geometry, true cost. Push includes `temperature` normalization inside S; *do
not* assume `S.IsKernel.total` normalizes wrt U at V given. Ceiling costs `Strong` only for finite
period here. The absolute lower bound in compact lane can be extraordinarily weak. Supplying
usable relative/stencil estimates stays required even with the algebraic error identity. Per-tag
positivity & normalized Haar formula later may help for an additional probe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Normal
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree YM.Push.SectorMeasure
open YM.Marker YM.Multi Order Integral Actual
open YM.Push.BetaTransport
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : Rep G f} {O : ChartRatio G}
  (J : Config G c) {R : ℝ}

/-- Analytical premise JUST for the actual relative probability readings. Uniform at fixed-volume.
  Usually a *relative to background weight* lower bound is needed in estimates; leave `Strong`
  for existence of operations; don't infer lack of large-volume cost. -/
structure Strong (f : Side) (U : Config G f→ℝ) : Prop where
  safe : Envelope U
  bound : ∃ C : ℝ, 0<C ∧ ∀ x,C≤ U x
namespace Strong
variable {W : Config G f→ℝ} (h : Strong f W) (x : Config G f)
include h
lemma positive : 0<W x := (h.bound.choose_spec.1).trans_le (h.bound.choose_spec.2 x)
lemma inv_env : Envelope (fun x => (W x)⁻¹) := by
   obtain ⟨C,H,H'⟩:= h.bound
   refine ⟨h.safe.meas.inv,C⁻¹,fun x=>?_⟩
   rw [Real.norm_of_nonneg (inv_pos.mpr (h.positive x)).le]; exact inv_anti₀ H (H' x)
lemma total_pos : 0 < ∫ x, W x ∂prior G f := by
   apply (integral_pos_iff_support_of_nonneg (fun x=>(h.positive x).le) (h.safe.integrable _)).2
   simp_rw [show Function.support W=Set.univ from Set.eq_univ_of_forall (fun x=>(h.positive x).ne')]; simp
end Strong
section bounds
variable (S) (hB : S.patch.Branches S.kernel G) {W : Config G f→ℝ} (hw : ∀ x,0≤ W x) {β : ℝ} (hm : Integrable W (prior G f))
include hB hm hw
/-- Expense of floor positivity. Available from one step explicitly, no recursion needed.
    NOT asserting this cost is usable in asymptotic polynomial error estimates.
     Use global factor only for local proofs at fixed geometry. Holds each β, R. -/
lemma positivity_budget (he : |β| ≤ R) : (noiseCost S R)⁻¹ * (∫ x,W x ∂prior G f) ≤
   S.push β W J := by
   rw [← integral_const_mul]; apply integral_mono (hm.const_mul _) (StepData.push_slice (S.isKernel hB _) _ _ hm)
   intro x; exact mul_le_mul_of_nonneg_right ((density_bounds S hB he x J).1) (hw x)
omit hw hm in
lemma coefficient_margin (hw : Strong f W) (he : |β| ≤ R) : 0<S.push β W J := lt_of_lt_of_le (mul_pos (inv_pos.mpr (noiseCost_pos ..)) (Strong.total_pos hw)) (positivity_budget S J hB (fun x=>(hw.positive x).le) (hw.safe.integrable _) he)
end bounds

-- Supply from actual unmarked
variable (H : History G) (h : H.Selected) (N q m : ℕ)
include h in
theorem actual (hm : m ≤ N) : Strong (H.S.side m q) (H.rep N q m).eval := by
   have ht := fun i hi=> (H.rep N q i).envelope (h.represents N q i hi).good
   refine ⟨ht _ hm,?_⟩
   rcases hm.lt_or_eq with hx|rfl
   · have hB := (H.levels.blocks m q).branches
     let S:= H.levels.clock.op m q; let β:= H.β N q (m+1)
     let k := noiseCost S |β|
     rw [(h.steps N q m hx).1]
     have hz := partition_pos (n:=H.S.side N q) (H.β N q N) (G:=G)
     refine ⟨k⁻¹*Wilson.partition G _ _,mul_pos (inv_pos.mpr (noiseCost_pos ..)) hz, fun x=> ?_⟩
     rw [← H.partition_eq h N q _ hx]
     exact positivity_budget S x hB (fun x=>(AxisShift.chosen_positive h hx x).le) ((ht _ hx).integrable _) (le_refl _)
   rw [(h.starts ..).2]
   obtain ⟨x,-,Hx⟩:=isCompact_univ.exists_isMinOn (s:=Set.univ) Set.univ_nonempty
      ((bare_cont (H.β m q m) (n:=H.S.side m q) (G:=G)).continuousOn)
   exact ⟨_,bare_pos _ x,fun y=>Hx (Set.mem_univ _)⟩
end YM.Comparison.RG02.Normal
