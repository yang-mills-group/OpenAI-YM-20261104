import YM.LocalLTE.Taylor
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Lens
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Nuts

/-! Post-L proof for the FULL triangular local comparison. This picks an actual
D-growing family of central integral functions (not a dissection of products
using independent ballots). Fixed-order and in the auxiliary size range only,
but that range grows unboundedly (needed for gluing the complete supports).
This file does not cover inheritance, nor conclude on physical lattice itself.
D enters coefficient prescription; later diagram comparisons e.g. removing
cutoff ball for coefficients have to retain this dependence. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Bid ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat Lantern Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius

/-- Strengthen Lantern.lookingGlass to arbitrary-order working **in the
actual b,V chart jointly**. Smooth pricing receipt uniform signature.
Prices and setup proofs all at stage, not per-step compactness. -/
theorem sapphire (G:Gauge) (L : Side) (j : ℕ) (p r : ℝ → ℝ)
    (hj : 1 ≤ j) (hp : Rate G L 0 p) {d c : ℝ} (hr : Bolt G L r) (hd : 0 < d) (hc : 0<c):
    ∃ b : ℝ → ℝ,Rate G L 0 b ∧ ∀ᶠ t in atTop, let D:= wick G L d t; let s:= eaves G L t
      ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
          (ι:Type) [Fintype ι] [DecidableEq ι] (ϕ ψ:E× Poll.Body ι→ℝ) (ρ:E→Poll.Body ι) (M:E→ Matrix ι ι ℝ),
          (Fintype.card ι:ℝ) ≤ r t → Golf ϕ ψ ρ M j D s s (p t) →
          (∀ z:ι→ℝ,dotProduct z ((M 0)⁻¹ *ᵥ z) ≤ c*dotProduct z z) →
          ∀ x ∈ ball (0:ℝ×E) s, Brush j (b t) 1 (cleanLog ϕ ψ ρ M D) x:= by
  -- Lens bound shortened, keep simultaneous derivatives
  obtain ⟨C,hC,H⟩:=Brush.compact (f:=Real.exp) (k:=j) (s:=Icc (-1:ℝ) 1) isCompact_Icc fun x _=> Real.contDiff_exp.contDiffAt
  let a₀:=Real.exp (-1)*(1/2); have h₀ : 0 < a₀:=by unfold a₀; positivity
  obtain ⟨Y,hY,hR⟩:=Brush.compact (f:=Real.log) (k:=j) (s:=Icc a₀ (Real.exp 1)) isCompact_Icc fun x hx=> Real.contDiffAt_log.mpr (h₀.trans_le hx.1).ne'
  let D t:= wick G L d t; let B t:= clump j (clump j (fee j (p t) (D t)) C) Y
  have hh := fareRate j hp (Rate.monitor.mul_left d)
  have he : Rate G L 0 B := lumpRate j (lumpRate j hh (Rate.const _)) (Rate.const _)
  have hw:= ((Brim.absolut hh).mul (Sienna.edge G L)).below (by linarith [vow_ok]) 1 zero_lt_one
  let f t := betaF G t L ^ (-1:ℝ)
  refine ⟨B,he,?_⟩
  filter_upwards [hw,Lantern.walls G L hr hc hd (-1:ℝ), (Rate.power (G:=G) (L:=L) (a:=-1)).below (by norm_num) (1/2) (by norm_num)] with t hx hz hv d₀ s E _ _ _ ι _ _ ϕ ψ ρ M hL hU ha x he
  have h' := mem_ball_zero_iff.mp he
  have h0 : ‖(0:E)‖< s:= by rw [norm_zero]; exact hU.pos
  have hs : 1/2≤(sweep (M 0)⁻¹).real (closedBall (0:Poll.Body ι) d₀):= by
    have he:= hz _ _ hL (hU.gram 0 h0).1.inv ha
    have hh': 1 - (sweep (M 0)⁻¹).real (closedBall (0:Poll.Body ι) d₀) ≤ 1/2:= le_trans he ((le_abs_self _).trans hv)
    linarith only [hh']
  apply lifted _ hU ((norm_snd_le x).trans_lt h') ((norm_fst_le x).trans_lt h') hj ?_ H hC.le hR hs
  rw [max_self]; exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) hU.pos.le) ((le_abs_self _).trans hx)
end YM.LocalLTE
