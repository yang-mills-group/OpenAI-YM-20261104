import YM.Integration.ActualRunCouplingChart

/-!
Composition of the exact signed non-affine coupling chart. Finite iteration
uses the original Run's adjacent beta differences and keeps cutoff and
period fixed. Its domain records every positive prefix radicand. The actual
positive regulators satisfy that domain without an inverse-neighborhood
assumption. A fixed field coordinate is carried literally unchanged.

These are parameter-map identities. They do not identify physical models,
jets, prices, or the field spaces at different Wilson scales.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NonAffineCouplingReset
open Filter
open scoped Topology

def radicand (delta h : ℝ) : ℝ := 1 - delta * h ^ 2
def unit (delta h : ℝ) : ℝ := (Real.sqrt (radicand delta h))⁻¹
def reset (delta h : ℝ) : ℝ := h * unit delta h

/-- The second denominator is the total denominator divided by the first. -/
theorem radicand_comp (a b h : ℝ) (ha : 0 < radicand a h) :
    radicand b (reset a h) = radicand (a + b) h / radicand a h := by
  change 1 - b * (h * (Real.sqrt (radicand a h))⁻¹) ^ 2 =
    radicand (a + b) h / radicand a h
  rw [mul_pow, inv_pow, Real.sq_sqrt ha.le]
  unfold radicand at *
  rw [div_eq_mul_inv]
  have hi := mul_inv_cancel₀ ha.ne'
  linear_combination -hi

/-- The compensating units compose even at h=0. Only the first radicand
must be positive for this totalized algebraic identity. -/
theorem unit_cocycle (a b h : ℝ) (ha : 0 < radicand a h) :
    unit a h * unit b (reset a h) = unit (a + b) h := by
  unfold unit
  rw [radicand_comp a b h ha, Real.sqrt_div' _ ha.le, inv_div,
    div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne',
    one_mul]

/-- Exact scalar composition, with no linearization of the reset. -/
theorem reset_comp (a b h : ℝ) (ha : 0 < radicand a h) :
    reset b (reset a h) = reset (a + b) h := by
  change (h * unit a h) * unit b (reset a h) = h * unit (a + b) h
  rw [mul_assoc, unit_cocycle a b h ha]

private theorem radicand_pos_germ (delta : ℝ) :
    ∀ᶠ h : ℝ in 𝓝 0, 0 < radicand delta h := by
  have hc : ContinuousAt (radicand delta) 0 := by
    unfold radicand
    fun_prop
  have hp : (0 : ℝ) < radicand delta 0 := by norm_num [radicand]
  exact hc.eventually (lt_mem_nhds hp)

/-- For arbitrary signed coefficients the two maps have the same germ. -/
theorem reset_comp_germ (a b : ℝ) :
    (fun h => reset b (reset a h)) =ᶠ[𝓝 0] reset (a + b) := by
  filter_upwards [radicand_pos_germ a] with h hh
  exact reset_comp a b h hh

def fieldReset {E : Type*} (delta : ℝ) (x : ℝ × E) : ℝ × E :=
  (reset delta x.1, x.2)

/-- The fixed field coordinate is retained, rather than suppressed. -/
theorem field_comp {E : Type*} (a b : ℝ) (x : ℝ × E)
    (ha : 0 < radicand a x.1) :
    fieldReset b (fieldReset a x) = fieldReset (a + b) x :=
  Prod.ext (reset_comp a b x.1 ha) rfl

end YM.Integration.NonAffineCouplingReset

namespace YM.Integration.ActualRunCouplingComposition
open Filter PhysicalNext.Repeat.Legato Pert.Asymptotics
open MatchingLedger.Compass.Income
open NonAffineCouplingReset
open ActualRunCouplingChart (betaDifference incoming)
open scoped Topology BigOperators

variable {G : Gauge} (R : Run G) (N p : ℕ)

def betaGap (start length : ℕ) : ℝ :=
  R.family.path.β N p start - R.family.path.β N p (start + length)

/-- Positive denominators at every prefix, including the final endpoint. -/
def Domain (start length : ℕ) (h : ℝ) : Prop :=
  ∀ j, j ≤ length → 0 < radicand (betaGap R N p start j) h

/-- Literal recursion through the existing actual adjacent incoming chart. -/
def iterate (start length : ℕ) (h : ℝ) : ℝ :=
  Nat.rec h (fun k value => incoming R N p (start + k) value) length

private theorem betaGap_succ (start k : ℕ) :
    betaGap R N p start k + betaDifference R N p (start + k) =
      betaGap R N p start (k + 1) := by
  unfold betaGap betaDifference
  simp only [Nat.add_succ]
  ring

/-- The coefficient is the sum of the original adjacent beta differences. -/
theorem betaDifference_sum (start length : ℕ) :
    ∑ j ∈ Finset.range length, betaDifference R N p (start + j) =
      betaGap R N p start length := by
  induction length with
  | zero => simp [betaGap]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, betaGap_succ]

/-- No reset axiom: the original adjacent maps compose by the proved
non-affine identity on the explicit positive-prefix domain. -/
theorem interval_eq (start length : ℕ) (h : ℝ)
    (hD : Domain R N p start length h) :
    iterate R N p start length h = reset (betaGap R N p start length) h := by
  revert hD
  induction length with
  | zero =>
      intro _
      simp [iterate, betaGap, reset, unit, radicand]
  | succ k ih =>
      intro hD
      have hprev : Domain R N p start k h := fun j hj =>
        hD j (hj.trans (Nat.le_succ k))
      change reset (betaDifference R N p (start + k))
        (iterate R N p start k h) = _
      rw [ih hprev, reset_comp _ _ _ (hD k (Nat.le_succ k)), betaGap_succ]

private theorem domain_germ (start length : ℕ) :
    ∀ᶠ h : ℝ in 𝓝 0, Domain R N p start length h := by
  induction length with
  | zero =>
      filter_upwards [] with h
      intro j hj
      have hz : j = 0 := by omega
      subst j
      simp [betaGap, radicand]
  | succ k ih =>
      have hp : ∀ᶠ h : ℝ in 𝓝 0,
          0 < radicand (betaGap R N p start (k + 1)) h :=
        NonAffineCouplingReset.radicand_pos_germ _
      filter_upwards [ih, hp] with h hprev hlast
      intro j hj
      by_cases hjk : j ≤ k
      · exact hprev j hjk
      have he : j = k + 1 := by omega
      simpa only [he] using hlast

/-- Every fixed finite interval gives the same signed germ at zero. -/
theorem interval_germ (start length : ℕ) :
    iterate R N p start length =ᶠ[𝓝 0] reset (betaGap R N p start length) := by
  filter_upwards [domain_germ R N p start length] with h hh
  exact interval_eq R N p start length h hh

private theorem actual_radicand (start length : ℕ) (hs : start ≤ N) :
    radicand (betaGap R N p start length) (regulatorRun R.family N p start) =
      R.family.path.β N p (start + length) / R.family.path.β N p start := by
  have hc := Weather.iceborn R.family R.makes hs p
  have hsq : regulatorRun R.family N p start ^ 2 =
      (R.family.path.β N p start)⁻¹ := by
    unfold regulatorRun
    rw [inv_pow, Real.sq_sqrt hc.le]
  rw [radicand, hsq, betaGap]
  field_simp [hc.ne']; ring

/-- Every prefix denominator is positive at the actual original regulator. -/
theorem actual_domain (start length : ℕ) (hN : start + length ≤ N) :
    Domain R N p start length (regulatorRun R.family N p start) := by
  intro j hj
  have hs : start ≤ N := by omega
  have hjN : start + j ≤ N := by omega
  rw [actual_radicand R N p start j hs]
  exact div_pos (Weather.iceborn R.family R.makes hjN p)
    (Weather.iceborn R.family R.makes hs p)

/-- The full interval reset maps the actual starting coupling to the actual
ending coupling. Both are positive on the same cutoff and period. -/
theorem reset_actual (start length : ℕ) (hN : start + length ≤ N) :
    reset (betaGap R N p start length) (regulatorRun R.family N p start) =
      regulatorRun R.family N p (start + length) := by
  have hs : start ≤ N := by omega
  have hc := Weather.iceborn R.family R.makes hs p
  have hf := Weather.iceborn R.family R.makes hN p
  change regulatorRun R.family N p start *
    (Real.sqrt (radicand (betaGap R N p start length)
      (regulatorRun R.family N p start)))⁻¹ = _
  rw [actual_radicand R N p start length hs]
  unfold regulatorRun
  rw [Real.sqrt_div' _ hc.le]
  field_simp [(Real.sqrt_pos.mpr hc).ne', (Real.sqrt_pos.mpr hf).ne']

/-- Repeated use of the original adjacent chart has the exact actual endpoint. -/
theorem interval_actual (start length : ℕ) (hN : start + length ≤ N) :
    iterate R N p start length (regulatorRun R.family N p start) =
      regulatorRun R.family N p (start + length) := by
  rw [interval_eq R N p start length _ (actual_domain R N p start length hN)]
  exact reset_actual R N p start length hN

def fieldIterate {E : Type*} (start length : ℕ) (x : ℝ × E) : ℝ × E :=
  (iterate R N p start length x.1, x.2)

/-- The parameter identity holds on the full product with any fixed field. -/
theorem field_interval {E : Type*} (start length : ℕ) (x : ℝ × E)
    (hD : Domain R N p start length x.1) :
    fieldIterate R N p start length x =
      fieldReset (betaGap R N p start length) x :=
  Prod.ext (interval_eq R N p start length x.1 hD) rfl

/-- Actual same-Run endpoints with the field coordinate literally unchanged. -/
theorem field_actual {E : Type*} (start length : ℕ) (hN : start + length ≤ N)
    (U : E) :
    fieldIterate R N p start length (regulatorRun R.family N p start, U) =
      (regulatorRun R.family N p (start + length), U) :=
  Prod.ext (interval_actual R N p start length hN) rfl

end YM.Integration.ActualRunCouplingComposition
end
