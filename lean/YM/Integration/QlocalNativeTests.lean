import YM.Integration.LocalComparisonInterface
import YM.Integration.RG05IndependentTests

/-! Native independent smooth tests in the exact qlocal address space.
The Euclidean-to-maximum coordinate map retains its fixed derivative cost.
Each original test budget remains separate, including zero budgets. A
single given multilinear functional is evaluated throughout. The native
affine chain rule retains its literal rate at every derivative order. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.QlocalNativeTests
open Function Finset ComparisonDensity.Address RG05Readout.Native RG05Readout.Nuclear
open LocalComparison RG3.Held
open scoped Topology ContDiff BigOperators Classical

def coordinates : Pos ≃L[ℝ] E4 :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Axis => ℝ)).symm

def pulled (f : Body) : Pos → ℂ := f.val ∘ coordinates

def orbit (order weight : ℕ) : Orbit := ⟨.whole, order, weight⟩

/-- The literal four-coordinate map has operator norm at most two. -/
theorem coordinates_norm : ‖coordinates.toContinuousLinearMap‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound coordinates.toContinuousLinearMap (by norm_num)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (norm_nonneg x))).mp
  change ‖(WithLp.toLp 2 x : E4)‖ ^ 2 ≤ (2 * ‖x‖) ^ 2
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    ∑ a : Axis, ‖x a‖ ^ 2 ≤ ∑ _a : Axis, ‖x‖ ^ 2 :=
      Finset.sum_le_sum (fun a _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm x a) 2)
    _ = (2 * ‖x‖) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Every stipulated native derivative is paid before converting a slot
to the weighted whole-space address norm. -/
theorem tall_bill (d w : ℕ) (f : Body) {c : ℝ}
    (h : Tall (E := E4) f d 1 c) :
    (orbit d w).Bill (pulled f) ((2 : ℝ) ^ d * c) := by
  have hc : 0 ≤ c := RG05IndependentTests.tall_budget_nonneg h
  refine ⟨mul_nonneg (pow_nonneg (by norm_num) _) hc,
    (body_smooth f d).comp coordinates.contDiff, ?_⟩
  intro k hk x _hx
  change ‖iteratedFDeriv ℝ k (f.val ∘ coordinates.toContinuousLinearMap) x‖ ≤ _
  rw [coordinates.toContinuousLinearMap.iteratedFDeriv_comp_right
    (body_smooth f d) x (by exact_mod_cast hk)]
  have he := (iteratedFDeriv ℝ k f.val (coordinates x)).norm_compContinuousLinearMap_le
    (fun _ : Fin k => coordinates.toContinuousLinearMap)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  have hp : ‖coordinates.toContinuousLinearMap‖ ^ k ≤ (2 : ℝ) ^ d :=
    (pow_le_pow_left₀ (norm_nonneg _) coordinates_norm k).trans
      (pow_le_pow_right₀ (by norm_num) hk)
  have hf : ‖iteratedFDeriv ℝ k f.val (coordinates x)‖ ≤ c := by
    simpa only [one_pow, one_mul] using h k hk (coordinates x)
  have hw : 1 ≤ (orbit d w).height x := by
    exact one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg x))
  calc
    _ ≤ ‖iteratedFDeriv ℝ k f.val (coordinates x)‖ *
        ‖coordinates.toContinuousLinearMap‖ ^ k := he
    _ ≤ c * (2 : ℝ) ^ d :=
      mul_le_mul hf hp (pow_nonneg (norm_nonneg _) _) hc
    _ = (2 : ℝ) ^ d * c := mul_comm _ _
    _ ≤ (orbit d w).height x * ((2 : ℝ) ^ d * c) :=
      le_mul_of_one_le_left (mul_nonneg (pow_nonneg (by norm_num) _) hc) hw

/-- A zero native whole-space budget gives the original zero function. -/
theorem tall_zero (d : ℕ) (f : Body) (h : Tall (E := E4) f d 1 0) :
    f.val = 0 := by
  funext x
  apply norm_le_zero_iff.mp
  simpa only [norm_iteratedFDeriv_zero, one_pow, mul_zero] using h 0 (Nat.zero_le d) x

/-- Normalize one slot, preserving its exact original budget factor. -/
theorem normalize (d w : ℕ) (f : Body) {c : ℝ}
    (h : Tall (E := E4) f d 1 c) :
    ∃ x : {q : Pos → ℂ // (orbit d w).Bill q 1},
      pulled f = (((2 : ℝ) ^ d * c : ℝ) : ℂ) • x.val := by
  by_cases hc : 0 < c
  · let b : ℝ := (2 : ℝ) ^ d * c
    have hb : 0 < b := mul_pos (pow_pos (by norm_num) _) hc
    let q : Pos → ℂ := (b : ℂ)⁻¹ • pulled f
    have hnorm : ‖(b : ℂ)⁻¹‖ * b = 1 := by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg hb.le, inv_mul_cancel₀ hb.ne']
    have hq := (tall_bill d w f h).smul (b : ℂ)⁻¹
    change (orbit d w).Bill q (‖(b : ℂ)⁻¹‖ * b) at hq
    rw [hnorm] at hq
    refine ⟨⟨q, hq⟩, ?_⟩
    change pulled f = (b : ℂ) • ((b : ℂ)⁻¹ • pulled f)
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hb.ne'), one_smul]
  · have hc0 : c = 0 :=
      le_antisymm (le_of_not_gt hc) (RG05IndependentTests.tall_budget_nonneg h)
    subst c
    refine ⟨⟨0, (Orbit.Bill.zero (U := orbit d w)).more zero_le_one⟩, ?_⟩
    simp only [mul_zero, Complex.ofReal_zero, zero_smul]
    exact congrArg (fun q : E4 → ℂ => q ∘ coordinates) (tall_zero d f h)

def nativeTest (d w : ℕ) (f : Body) {c : ℝ}
    (h : Tall (E := E4) f d 1 c) : (orbit d w).Mood :=
  ⟨pulled f, ⟨(2 : ℝ) ^ d * c, tall_bill d w f h⟩⟩

/-- Every slot keeps its own function and budget; the unit tuple is chosen
once and can be supplied to any already fixed qlocal functional. -/
theorem independent_normalization {V : Type}
    (d w : V → ℕ) (f : V → Body) (c : V → ℝ)
    (h : ∀ v, Tall (E := E4) (f v) (d v) 1 (c v)) :
    ∃ x : IndependentTests (fun v => orbit (d v) (w v)), ∀ v,
      nativeTest (d v) (w v) (f v) (h v) =
        (((2 : ℝ) ^ d v * c v : ℝ) : ℂ) •
          testInclusion (fun v => orbit (d v) (w v)) x v := by
  choose x hx using fun v => normalize (d v) (w v) (f v) (h v)
  refine ⟨x, fun v => ?_⟩
  apply Subtype.ext
  exact hx v

private theorem letter_scale_all {V : Type} [DecidableEq V]
    {T : V → Type} [∀ v, AddCommGroup (T v)] [∀ v, Module ℂ (T v)]
    {E : Type} [AddCommGroup E] [Module ℂ E] {s : Finset V}
    {F : (∀ v, T v) → E} (h : Letter ℂ T s F)
    (a : V → ℂ) (x : ∀ v, T v) :
    F (fun v => a v • x v) = (∏ v ∈ s, a v) • F x := by
  let y (p : Finset V) (v : V) := if v ∈ p then a v • x v else x v
  have hp : ∀ p : Finset V, p ⊆ s → F (y p) = (∏ v ∈ p, a v) • F x := by
    intro p
    induction p using Finset.induction_on with
    | empty =>
        intro _
        simp only [y, Finset.notMem_empty, if_false, Finset.prod_empty, one_smul]
    | @insert i p hi ih =>
        intro hs
        have hiS : i ∈ s := hs (Finset.mem_insert_self i p)
        have he : y (insert i p) = update (y p) i (a i • x i) := by
          funext v
          by_cases hv : v = i
          · subst v
            simp [y]
          · simp [y, hv]
        have hy : update (y p) i (x i) = y p := by
          have hh : y p i = x i := if_neg hi
          rw [← hh, update_eq_self]
        rw [he, h.scale _ i hiS, hy,
          ih (Finset.insert_subset_iff.mp hs).2, Finset.prod_insert hi, smul_smul]
  exact (h.stay _ _ (fun v hv => (if_pos hv).symm)).trans (hp s (Finset.Subset.refl s))

/-- Exact coefficient conversion for one fixed multilinear functional.
The product uses precisely its declared marker mode, including zero slots. -/
theorem coefficient_normalization {V : Type} [DecidableEq V]
    (d w : V → ℕ) {E : Type} [AddCommGroup E] [Module ℂ E]
    (s : Finset V) (F : TestSpace (fun v => orbit (d v) (w v)) → E)
    (hF : Letter ℂ (fun v => (orbit (d v) (w v)).Mood) s F)
    (f : V → Body) (c : V → ℝ)
    (h : ∀ v, Tall (E := E4) (f v) (d v) 1 (c v)) :
    ∃ x : IndependentTests (fun v => orbit (d v) (w v)),
      F (fun v => nativeTest (d v) (w v) (f v) (h v)) =
        (∏ v ∈ s, (((2 : ℝ) ^ d v * c v : ℝ) : ℂ)) •
          F (testInclusion (fun v => orbit (d v) (w v)) x) := by
  obtain ⟨x, hx⟩ := independent_normalization d w f c h
  refine ⟨x, ?_⟩
  rw [funext hx]
  exact letter_scale_all hF _ _

/-- The original affine address map keeps its literal mesh/radius rate
at every derivative order, before any common envelope is applied. -/
theorem affine_jet (Y : Dip) (f : Body) (k : ℕ) (x : Pos) :
    iteratedFDeriv ℝ k (Y.plant (pulled f)) x =
      Y.rate ^ k • iteratedFDeriv ℝ k (pulled f) (Y.arc x) :=
  Y.links k ((body_smooth f k).comp coordinates.contDiff) x


/-- The address pull is exactly the original native Euclidean test pull,
with the same shift and scalar rate. -/
theorem affine_native (Y : Dip) (f : Body) :
    Y.plant (pulled f) =
      pulled (RG05Readout.Native.pull (coordinates Y.shift) Y.rate f) := by
  funext x
  change f.val (coordinates (Y.shift + Y.rate • x)) =
    f.val (coordinates Y.shift + Y.rate • coordinates x)
  rw [map_add, map_smul]

end YM.Integration.QlocalNativeTests
