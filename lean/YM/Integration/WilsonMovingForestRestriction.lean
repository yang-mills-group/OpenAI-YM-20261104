import YM.FormalBulk08.Primer.Kernel

/-! Full coupling-order evaluation of the prescribed fine forest section.
It preserves the whole old polynomial, its actual unmarked block potential
and its original Haar Jacobian at each finite joint field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingForestRestriction
open Function PowerSeries Lattice Exterior Wilson RG Precision Tree Bloch
open FormalBulk08 Jets Series Wick Orb Reef Flat
open scoped Classical ContDiff
variable {I V : Type} [Fintype I] [Fintype V]

theorem pull (m : Jets.Rays V → Jets.Rays I) (regular : ContDiffAt ℝ ∞ m 0)
    (linear : ∀ (t : ℝ) v, m (t • v)=t • m v) (x : Jets.Rays V) (i : I) :
    glimpse x (motor m i) = PowerSeries.C (m x i) := by
  have fixed := fixed_path x (fun v => m v i) (coord_diff m regular i)
  have ray : glimpse x (paste (fun v => m v i)) = X^1 * C (m x i) := by
    apply unique_gaze fixed
    simpa only [linear, pow_one, Pi.smul_apply, smul_eq_mul] using (gaze_leaf (m x i) 1)
  ext n
  rw [glimpse_coeff, motor, after_one, ← glimpse_coeff, ray, coeff_X_pow_mul']
  simp

theorem complete (m : Jets.Rays V → Jets.Rays I) (regular : ContDiffAt ℝ ∞ m 0)
    (linear : ∀ (t : ℝ) v, m (t • v)=t • m v) (x : Jets.Rays V) (T : Pap I) :
    glimpse x (roam ℝ (motor m) T) = glimpse (m x) T := by
  rw [glimpse_slide]
  have entries : (fun i => glimpse x (motor m i)) = PowerSeries.C ∘ (m x) :=
    funext (pull m regular linear x)
  rw [entries, roam, const_insertAt, pure_map]
  rfl

variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

theorem seat (x : Jets.Rays (Pine G S F ⊕ wire G c)) (p : Pap (wire G f)) :
    glimpse x (Reef.seat F p) = glimpse (Reef.offer G F (x ∘ Sum.inl)) p := by
  rw [Reef.seat, complete (graft F) ((graft_receipt F).of_le le_top)
    (fun t v => graft_linear F v t)]
  ext i
  simp only [glimpse_coeff, PowerSeries.coeff_map]
  unfold traceP
  change MvPolynomial.aeval (graft F x) (MvPolynomial.rename Sum.inl (coeff i p)) = _
  rw [MvPolynomial.aeval_rename]
  rfl

theorem prepared (p : Pap (wire G f)) (branch : S.patch.Branches S.kernel G)
    (t : S.Choices) (O : ChartRatio G) (ratio : LocalRatio O)
    (x : Jets.Rays (Pine G S F ⊕ wire G c)) :
    X^2 * glimpse x (Reef.flush F t O p) =
      X^2 * glimpse (Reef.offer G F (x ∘ Sum.inl)) p -
        glimpse x (Jets.paste (Reef.clack S t ∘ Reef.graft F)) +
      X^2 * glimpse x (Jets.paste (Real.log ∘
        (fun v : Jets.Rays (Pine G S F ⊕ wire G c) => Reef.sap F O (v ∘ Sum.inl)))) := by
  have h := congrArg (glimpse x) (Primer.prepare S F p branch t ratio)
  rw [← seat F x p]
  simpa only [glimpse, map_mul, map_pow, map_add, map_sub, PowerSeries.map_X] using h

end YM.Integration.WilsonMovingForestRestriction
end
