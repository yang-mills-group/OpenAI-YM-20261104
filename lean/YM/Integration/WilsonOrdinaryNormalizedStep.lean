import YM.Integration.WilsonOrdinaryMixedDetectors

/-! Read the true normalized dilation, at a fixed positive ratio, from the same
finite physical reflected detectors. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryNormalizedStep
open Filter Spec Climb SharpGram Trace.Pilot WilsonOrdinaryMixedGram
open scoped Topology Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (J : ℝ → PhysMS.tower S) (d : ℕ)
set_option quotPrecheck false
local notation "D" => (Bel C.book).Field d

/-- Apply the same engineering factors as in `PhysMS.Frame.cocycle_value` before
reading the proposed normalized step on the real second-leg Gram. -/
def trialStep (r t : ℝ) (A : D →ₗ[ℂ] D) : RealForm D D :=
  trial F J d r (((Pert.Scale.gear C.labels d t).comp A).restrictScalars ℝ)

theorem from_scalar (P : Pier.Lair.Present F J) (b : Module.Basis ι ℝ D) {t : ℝ} (ht : 0 < t) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ r in trail, ∀ A : D →ₗ[ℂ] D, ∀ ε : ℝ, 0 ≤ ε →
      (∀ i j : ι, |mixed F J d r (t*r) (b i) (b j) - trialStep F J d r t A (b i) (b j)| ≤ ε) →
      ∀ v : D, ‖PhysMS.Frame.cocycle d J r t ht v - A v‖ ≤ K * ε * ‖v‖ := by
  obtain ⟨K,hK,read⟩ := WilsonOrdinaryMixedDetectors.read_frame F J d P b
  let E := Pert.Scale.gearIso C.labels d t ht
  let g := E.symm.toLinearMap.toContinuousLinearMap
  refine ⟨max 1 ‖g‖ * K, mul_pos (zero_lt_one.trans_le (le_max_left ..)) hK, ?_⟩
  filter_upwards [read] with r hr A ε hε price v
  have reco := hr (t*r) (((Pert.Scale.gear C.labels d t).comp A).restrictScalars ℝ) ε hε price v
  let z := (J r d).symm (J (t*r) d v) - E (A v)
  have hz : ‖z‖ ≤ K*ε*‖v‖ := reco
  have eq : g z = PhysMS.Frame.cocycle d J r t ht v - A v := by
    change E.symm ((J r d).symm (J (t*r) d v) - E (A v)) = _
    rw [map_sub,LinearEquiv.symm_apply_apply]; rfl
  calc
    _ = ‖g z‖ := congrArg norm eq.symm
    _ ≤ ‖g‖ * ‖z‖ := g.le_opNorm z
    _ ≤ max 1 ‖g‖ * (K * ε * ‖v‖) := mul_le_mul (le_max_right ..) hz (norm_nonneg _) (zero_le_one.trans (le_max_left ..))
    _ = _ := by ring

/-- The actual normalized step through second order, with no direction frozen after
reading the detectors. A functional which kills its linear response sees only the
quadratic term and the measured residual. -/
def second (g : ℝ) (A B : D →ₗ[ℂ] D) : D →ₗ[ℂ] D :=
  LinearMap.id + (g:ℂ) • A + ((g:ℂ)^2) • B

theorem crossed {t : ℝ} (ht : 0 < t) (P : Pier.Lair.Present F J) (b : Module.Basis ι ℝ D)
    (g : ℝ → ℝ) (A B : D →ₗ[ℂ] D) (c : ℝ) (hc : 0 ≤ c)
    (table : ∀ᶠ r in trail, ∀ i j : ι,
      |mixed F J d r (t*r) (b i) (b j) - trialStep F J d r t (second d (g r) A B) (b i) (b j)| ≤ c*(g r)^2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ r in trail, ∀ (L : D →L[ℂ] ℂ) (v : D), L (A v) = 0 →
      ‖L (PhysMS.Frame.cocycle d J r t ht v) - L v‖ ≤ ‖L‖ * K * (g r)^2 * ‖v‖ := by
  obtain ⟨K,hK,read⟩ := from_scalar F J d P b ht
  let B' := B.toContinuousLinearMap
  refine ⟨K*c+‖B'‖,by positivity,?_⟩
  filter_upwards [read, table] with r hr hk L v killed
  let U := PhysMS.Frame.cocycle d J r t ht
  let V := second d (g r) A B
  have err := hr V (c*(g r)^2) (by positivity) hk v
  have quad : L (V v) - L v = ((g r:ℂ)^2) • L (B v) := by
    simp [V,second, killed]
  have bnd : ‖L (B v)‖ ≤ ‖L‖ * (‖B'‖ * ‖v‖) :=
    (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (B'.le_opNorm v) (norm_nonneg _))
  calc
    _ = ‖L (U v - V v) + (L (V v) - L v)‖ := by
      rw [map_sub]; apply congrArg norm; change L (U v) - L v = _; abel
    _ ≤ ‖L (U v - V v)‖ + ‖L (V v) - L v‖ := norm_add_le ..
    _ ≤ ‖L‖ * (K * (c * (g r)^2) * ‖v‖) + (g r)^2 * (‖L‖ * (‖B'‖ * ‖v‖)) := by
      apply add_le_add
      · exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left err (norm_nonneg _))
      · rw [quad,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
        exact mul_le_mul_of_nonneg_left bnd (sq_nonneg _)
    _ = _ := by ring

end YM.Integration.WilsonOrdinaryNormalizedStep
