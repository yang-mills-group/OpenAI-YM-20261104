import YM.Integration.ActualRunAdmissionScales
import YM.Integration.ActualRunFixedOrders
import YM.Integration.NativeRequestedInputNorm
import YM.IterationFour.Vacuum.Price

/-! At quadratic order the grading forces the additional masked list of every
prescribed plan to be empty. The original Wilson representation then gives
the full uniform unmarked receipt in its native exponent, at every cutoff. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OriginalQuadraticVacuum

open Filter Lattice Wilson RG IterationFour IterationFour.Vacuum IterationFour.Currency
open PhysicalNext.Repeat.Legato
open scoped Topology

variable {G : Gauge} {C : Family G}

/-- A supplied quadratic plan has no legally graded additional layers. -/
theorem layers_eq_nil {N period i : ℕ} (P : Plan C N period 2) (hi : i ≤ N) :
    P.layers i = [] := by
  cases h : P.layers i with
  | nil => rfl
  | cons e es =>
    have hmem : e ∈ P.layers i := by rw [h]; exact List.mem_cons_self
    obtain ⟨hlo, hhi⟩ := P.orders i hi e hmem
    omega

/-- Exact equality with the original full density, all forced rows, the
affine-null regular receipt at its native cost, and zero beta discrepancy. -/
theorem original_coin (hC : C.Makes) {N period i : ℕ}
    (P : Plan C N period 2) (hi : i ≤ N) :
    Coin C N period i (P.layers i) (C.path.rep N period i)
      (weight C.path.levels (11/5) i) (C.path.levels.clock.forcedAllowance i) 0 := by
  rw [layers_eq_nil P hi]
  have h := hC.wilson.represents N period i hi
  refine ⟨⟨rfl, h.clip, h.vac⟩, ?_, ?_, ?_, rfl, ?_⟩
  · exact h.vac ▸ h.good.labels
  · exact h.vac ▸ h.good.labels
  · intro e he
    simp at he
  · simp

/-- One bound before all period, cutoff, and prescribed plan choices. -/
theorem uniform (hC : C.Makes) (i N period : ℕ) (hi : i ≤ N)
    (P : Plan C N period 2) :
    Coin C N period i (P.layers i) (C.path.rep N period i)
      ((2 : ℝ) ^ (11/5 : ℝ) * g C N period i ^ (11/5 : ℝ))
      (C.path.levels.clock.forcedAllowance i) 0 :=
  (original_coin hC P hi).enlarge (g_weight hC hi (11/5) (by norm_num)).1

/-- The native exponent pays every smaller nonnegative error exponent with
any epsilon on a single tail before all regulators and all quadratic plans. -/
theorem eventual_small (hG : G.Simple) (hC : C.Makes) {s ε : ℝ}
    (hs : 0 ≤ s) (hs' : s < 11/5) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N period : ℕ, i ≤ N → ∀ P : Plan C N period 2,
      Coin C N period i (P.layers i) (C.path.rep N period i)
        (ε * g C N period i ^ s) (C.path.levels.clock.forcedAllowance i) 0 := by
  have h2 : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [buy C.path.levels hG 1 (div_pos hε h2) hs'] with i hpay N period hi P
  apply (original_coin hC P hi).enlarge
  calc
    weight C.path.levels (11/5) i ≤ ε / 2 ^ s * weight C.path.levels s i := by
      simpa only [one_mul] using hpay
    _ ≤ ε / 2 ^ s * (2 ^ s * g C N period i ^ s) :=
      mul_le_mul_of_nonneg_left (g_weight hC hi s hs).1 (div_nonneg hε.le h2.le)
    _ = ε * g C N period i ^ s := by rw [← mul_assoc, div_mul_cancel₀ _ h2.ne']

/-- On the original constructed profile, every fixed derivative and distance
order and support exponent up to the initial reserve admit the same physical
regular rows at the requested norm, together with the native forced cap. -/
theorem requested (R : Run G) (hG : G.Simple)
    (hprofile : ∀ j, j ≤ (R.metals.p.profile j).order ∧ j ≤ (R.metals.p.profile j).power)
    (ord pow : ℕ) (support : ℝ) (hord : 6 ≤ ord) (hpow : 2 ≤ pow) (hsupport : 0 < support)
    (hreserve : support ≤ (R.family.path.levels.budget 0).supportExponent)
    {s ε : ℝ} (hs : 0 ≤ s) (hs' : s < 11/5) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop, ∀ N period : ℕ, i ≤ N → ∀ P : Plan R.family N period 2,
      let V := R.family.path.rep N period i
      let cost := ε * g R.family N period i ^ s
      let requested := ActualRunAdmissionScales.requestedBudget R.family.path.levels i
        ord pow support hord hpow hsupport
      Coin R.family N period i (P.layers i) V cost
        (R.family.path.levels.clock.forcedAllowance i) 0 ∧
      (NativeRequestedInputNorm.regularPayload V.activities).Invoice requested cost := by
  filter_upwards [eventual_small hG R.makes hs hs' hε,
    R.family.path.levels.fits.deep.eventually_ge_atTop (max ord pow)] with i hcoin hlevel N period hi P
  obtain ⟨ho, hp⟩ := ActualRunFixedOrders.budget_orders R hprofile i
  have hS := hreserve.trans (R.family.path.levels.fits.deepExp (Nat.zero_le i))
  exact ⟨hcoin N period hi P, NativeRequestedInputNorm.regular_invoice
    (hcoin N period hi P).error rfl rfl (((le_max_left ord pow).trans hlevel).trans ho)
    (((le_max_right ord pow).trans hlevel).trans hp) hS⟩

end YM.Integration.OriginalQuadraticVacuum
