import YM.Integration.FVA1Physical.Sources.Round2.RootedExterior
import YM.Integration.FVA1Physical.Wilson.ExteriorRate
import YM.Integration.FVA1Physical.Wilson.ChartEnvelope

/-! On the physical `boxX` collar the emitted independent coefficient can
be computed after changing every exterior link, even by a globally rough
gauge field. The volume-free bound uses its full polynomial degree, the
complete derivative vault at zero, and the bounded native logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset MvPolynomial Lattice RG YM.Wilson Precision Exterior
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Bout MSbar.Mosaic MSbar.Measuring MSbar.Lis MSbar.Bakery
open Push Push.Uniform
open scoped Classical Topology
variable {σ : Type} [Fintype σ] {n : Side} {G : Gauge}

theorem rough_vault_motion (loc : σ→Site n) (b : Site n) (m s R : ℕ) {a B K : ℝ}
    (ha : 0 ≤ a) (f : Pot σ) (deg : f.totalDegree ≤ m)
    (paid : Vault loc {b} a s m 0 f B) (X Y : View σ) (hX : ‖X‖ ≤ K) (hY : ‖Y‖ ≤ K)
    (same : ∀ i, separation b (loc i)<R → X i=Y i) :
    |MvPolynomial.eval Y f-MvPolynomial.eval X f| ≤ 2*K*(B*(1+3*K)^(m+1))/liftW a s R := by
  let v:=Y-X
  have hK := (norm_nonneg X).trans hX
  have hv : ‖v‖ ≤ 2*K := (norm_sub_le ..).trans ((add_le_add hY hX).trans_eq (two_mul _).symm)
  have far (i : σ) (nz : v i ≠ 0) : R ≤ separation b (loc i) := by
    by_contra! bad
    exact nz (sub_eq_zero.mpr (same i bad).symm)
  have along (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) : ‖X+t•v-0‖ ≤ 3*K := by
    rw [sub_zero]
    apply (norm_add_le ..).trans
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    calc ‖X‖+t*‖v‖ ≤ K+1*(2*K) := add_le_add hX (mul_le_mul ht.2 hv (norm_nonneg _) zero_le_one)
         _ = _ := by ring
  have row:=Round2.Curvature.rooted_exterior_motion loc b s R ha f X v far
    (fun t ht=>Bout.across _ paid ha (along t ht) deg 1)
  have eqn : X+v=Y := add_sub_cancel _ _
  rw [eqn] at row
  exact row.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hv
    (mul_nonneg paid.1 (pow_nonneg (by positivity) _))) (wpos ..).le)

/-- Neither the threshold nor the collar error depends on the ambient torus,
the number of changed links or the distant rescaled values. -/
theorem rough_polynomial_collar (m s : ℕ) (C b Q : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ y : ℝ in atTop, ∀ (σ : Type) [Fintype σ] (n : Side) (loc : σ→Site n) (z : Site n)
      (g : ℝ), lensT y g → ∀ f : Pot σ, f.totalDegree ≤ m →
      Vault loc {z} (αm y) s m 0 f (y^b) → ∀ X Y : View σ,
      ‖X‖ ≤ |g⁻¹| *C → ‖Y‖ ≤ |g⁻¹| *C → (∀ i, loc i∈boxX y z → X i=Y i) →
      |MvPolynomial.eval Y f-MvPolynomial.eval X f| ≤ y^(-Q) := by
  filter_upwards [exterior_toll m s (2*C) b Q (by positivity),eventually_ge_atTop (1:ℝ)] with y toll y1
  intro σ _ n loc z g band f deg paid X Y hX hY same
  have cap : |g⁻¹| *C ≤ (2*C)*y :=
    (mul_le_mul_of_nonneg_right (inverse_clock_le_linear y1 band).2 hC).trans_eq (by ring)
  apply (rough_vault_motion loc z m s (spotN y) (zpow_nonneg (sq_nonneg _) _) f deg paid
    X Y (hX.trans cap) (hY.trans cap) ?_).trans toll
  exact fun i near=>same i (halo_spec.mpr ⟨z,mem_singleton_self _,near.le⟩)

/-- Genuine gauge configurations may be changed arbitrarily on exterior links.
Their native Wilson chart representative is automatically bounded by C/g. -/
theorem rough_configuration_collar (G : Gauge) (m s : ℕ) (b Q : ℝ) :
    ∀ᶠ y : ℝ in atTop, ∀ (n : Side) (z : Site n) (g : ℝ), lensT y g →
      ∀ f : Pot (Primary n G), f.totalDegree ≤ m →
      Vault (Measuring.chart n G) {z} (αm y) s m 0 f (y^b) → ∀ U V : Config G n,
      (∀ e : Edge (Site n), e.1∈boxX y z → U e=V e) →
      |MvPolynomial.eval (chartLog g V) f-MvPolynomial.eval (chartLog g U) f| ≤ y^(-Q) := by
  filter_upwards [rough_polynomial_collar m s (LocalH.geom_patch G).choose b Q
    (LocalH.geom_patch G).choose_spec.1.le] with y price
  intro n z g band f deg paid U V same
  apply price (Primary n G) n (Measuring.chart n G) z g band f deg paid
    (chartLog g U) (chartLog g V) (chartLog_norm_bound ..) (chartLog_norm_bound ..)
  intro i hi
  change g⁻¹*(logWithin G (U (rope i))) i.2=g⁻¹*(logWithin G (V (rope i))) i.2
  rw [same (rope i) hi]

end YM.Integration.FVA1Physical.Wilson
