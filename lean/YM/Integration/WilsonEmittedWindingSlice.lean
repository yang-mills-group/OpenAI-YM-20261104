import YM.Integration.WilsonEmittedCouplingSlice

/-! A finite-period low-jet discrepancy in the actual compact group word.
The derivatives at the origin enter once in unscaled units. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedWindingSlice
open Set Function Comparison.RG02 Comparison.Density
open AnalyticBridge.SectorAffine.Offset
open scoped ContDiff Classical
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem jet (f:E → F) {m J:ℕ} {g D ε:ℝ} (order:J ≤ m)
    (hg:0 ≤ g) (small:g ≤ 1) (hD:0 ≤ D) (hε:0 ≤ ε)
    (fund:∀ z:E,‖z‖ ≤ g → Through m f z D)
    (seam:∀ k < J,‖iteratedFDeriv ℝ k f 0‖ ≤ ε) :
    ∀  i k:ℕ,i+k=J  →  ∀  z:E,‖z‖ ≤ g  → 
      ‖iteratedFDeriv ℝ k f z‖ ≤ (i:ℝ)*ε+D*g^i  :=  by
  intro i
  induction i with
  | zero =>
    intro k joined z near
    have hk:k=J := by omega
    simpa using (fund z near).pay k (hk.le.trans order)
  | succ i ih =>
    intro k joined z near
    have hk:k < J := by omega
    let V := Metric.closedBall (0:E) g
    have mem (y:E):y∈V ↔ ‖y‖ ≤ g := by simp [V]
    let H := iteratedFDeriv ℝ k f
    have differentiable (y) (h:y∈V):DifferentiableAt ℝ H y := 
      (fund y ((mem y).1 h)).smooth.differentiableAt_iteratedFDeriv
        (Nat.cast_lt.mpr (hk.trans_le order))
    have step:‖H z-H 0‖ ≤ ((i:ℝ)*ε+D*g^i)*‖z‖ := by
      simpa only [sub_zero] using (convex_closedBall (0:E) g).norm_image_sub_le_of_norm_fderiv_le
        differentiable (fun y (h:y∈V)=>(norm_fderiv_iteratedFDeriv (𝕜 := ℝ)).trans_le
          (ih (k+1) (by omega) y ((mem y).1 h))) ((mem 0).2 (by simpa using hg)) ((mem z).2 near)
    have keep:0 ≤ (i:ℝ)*ε+D*g^i := by positivity
    have fee:((i:ℝ)*ε)*g ≤ (i:ℝ)*ε := mul_le_of_le_one_right (by positivity) small
    calc
      _ = ‖H 0+(H z-H 0)‖ := by rw [add_sub_cancel]
      _  ≤  ε+((i:ℝ)*ε+D*g^i)*g := (norm_add_le ..).trans
        (add_le_add (seam k hk) (step.trans (mul_le_mul_of_nonneg_left near keep)))
      _  ≤  _ := by rw [Nat.cast_succ,pow_succ]; nlinarith

theorem original (f:ℝ×E → F) {m J l:ℕ} {g D ε:ℝ}
    (order:J ≤ m) (depth:l ≤ J) (hg:0 ≤ g) (small:g ≤ 1) (hD:0 ≤ D) (hε:0 ≤ ε)
    (fund:∀ z:ℝ×E,‖z‖ ≤ g → Through m f z D)
    (seam:∀ k < J,‖iteratedFDeriv ℝ k f 0‖ ≤ ε) :
    ∀ i < l,‖iteratedFDeriv ℝ i (fun y:E=>f (g,y)) 0‖ ≤ (J:ℝ)*ε+D*g^(J-l)  :=  by
  intro i hi
  have near:‖((g,0):ℝ×E)‖ ≤ g := by simp [Prod.norm_def,abs_of_nonneg hg,hg]
  have card:i ≤ m := hi.le.trans (depth.trans order)
  apply (WilsonEmittedCouplingSlice.fixed (x := (0:E)) (t := g) (m := i) (f := f) ?_).pay i le_rfl
  refine ⟨(Transport.through_le (fund _ near) card).smooth,?_⟩
  intro k hki
  have hk:k ≤ l := hki.trans hi.le
  apply (jet f order hg small hD hε fund seam (J-k) k (by omega) _ near).trans
  exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le J k) hε)
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg small (by omega)) hD)

end YM.Integration.WilsonEmittedWindingSlice
