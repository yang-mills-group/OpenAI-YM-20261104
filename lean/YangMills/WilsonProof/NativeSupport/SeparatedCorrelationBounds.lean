import YangMills.WilsonProof.NativeSupport.MatchingSpec

/-! Compact pointwise forms of the two all-orders comparisons on the appointed
physical frame. The size of a field is its coefficient ℓ¹ norm in the fixed
Maxwell jet chart. It introduces no choice of scheme, basis or normalization
depending on the scale. -/
set_option autoImplicit false
noncomputable section

namespace YangMills.Matching

open Filter Set
open scoped BigOperators Topology Classical

variable {g : GaugeGroup} {B : Maxwell.Reference g}
variable {C : WilsonFamily g} {T : Hierarchy C}

/-- Sum of the absolute values of the actual polynomial coefficients in the
public Maxwell chart. The same polynomial has the same size in every cap. -/
def sectorMass {d : ℕ} (v : B.sector d) : ℝ :=
  ∑ m ∈ v.val.support, ‖MvPolynomial.coeff m v.val‖

theorem sectorMass_nonneg {d : ℕ} (v : B.sector d) : 0 ≤ sectorMass v :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- Every monomial read is a contractive reading in this norm. -/
theorem coeff_le_sectorMass {d : ℕ} (v : B.sector d) (m : B.toCoordinates.Key →₀ ℕ) :
    ‖MvPolynomial.coeff m v.val‖ ≤ sectorMass v := by
  classical
  by_cases hm : m ∈ v.val.support
  · exact Finset.single_le_sum (fun j _ => norm_nonneg (MvPolynomial.coeff j v.val)) hm
  · rw [MvPolynomial.notMem_support_iff.mp hm, norm_zero]
    exact sectorMass_nonneg v

/-- The size sees all output directions, including the scalar at horizon zero. -/
theorem sectorMass_eq_zero_iff {d : ℕ} (v : B.sector d) : sectorMass v = 0 ↔ v = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply MvPolynomial.ext
    intro m
    have hle := coeff_le_sectorMass v m
    rw [h] at hle
    simpa using norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))
  · rintro rfl
    simp [sectorMass]

/-- The full measured correlation minus the truncation of the converted MS
correlation at this same clock. -/
def correlationError (M : MSbar.Coefficients B) (S : Conversion B) (H : Measurement B T)
    {n : ℕ} (p : ℕ) (a : Fin n → Label B) (phase : Option T.Character)
    (o : Spacetime) (s : ℝ) (x : Points n) : ℂ :=
  T.correlation phase (H.inputs s a) (WithLp.toLp 2 fun i => o + s • x i) -
    ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val * S.correlation M k.val a x

/-- This is a vector in the original finite output sector. Both the physical
inverse frame and the formal inverse field series act on the full output. -/
def opeError (M : MSbar.Coefficients B) (S : Conversion B) (H : Measurement B T)
    {n : ℕ} (h p : ℕ) (a : Fin n → Label B) (o : Spacetime)
    (s : ℝ) (x : Points n) : B.sector h :=
  H.wilsonOPE s h a o x -
    ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val • S.ope M h k.val a x

/-- One eventual event and one bound hold over the full separated compact,
the input unit balls and all character phases, including the Wilson average.
The center and the finite demand are fixed before taking the UV tail.
The product of input sizes gives the estimates for arbitrary complex fields,
also when some incoming grade exceeds the output horizon. -/
structure CompactPointwise (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) : Prop where
  correlation (n p : ℕ) (d : Fin n → ℕ) (o : Spacetime) (K : Set (Points n))
      (compact : IsCompact K) (separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ phase : Option T.Character,
      ∀ (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      ‖correlationError M S H p (fun i => ⟨d i, v i⟩) phase o s x‖ ≤
        A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1)
  ope (n h p : ℕ) (d : Fin n → ℕ) (o : Spacetime) (K : Set (Points n))
      (compact : IsCompact K) (separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      sectorMass (opeError M S H h p (fun i => ⟨d i, v i⟩) o s x) ≤
        A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1)

/-- The single bound for the entire OPE output also holds simultaneously for
its whole complex dual unit ball. A covector of any other finite bound can
be rescaled. The tester is chosen after the UV event. -/
theorem CompactPointwise.opeDual {M : MSbar.Coefficients B} {S : Conversion B}
    {H : Measurement B T} (comparison : CompactPointwise M S H)
    (n h p : ℕ) (d : Fin n → ℕ) (o : Spacetime) (K : Set (Points n))
    (compact : IsCompact K) (separated : K ⊆ WilsonFamily.separated n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → B.sector (d i)) (x : Points n), x ∈ K →
      ∀ out : B.sector h →ₗ[ℂ] ℂ, (∀ w, ‖out w‖ ≤ sectorMass w) →
      ‖out (opeError M S H h p (fun i => ⟨d i, v i⟩) o s x)‖ ≤
        A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1) := by
  obtain ⟨A, hA, tail⟩ := comparison.ope n h p d o K compact separated
  refine ⟨A, hA, ?_⟩
  filter_upwards [tail] with s hs
  exact fun v x hx out hbound => (hbound _).trans (hs v x hx)

/-- Optional Euclidean shape-jet estimate on a specified representative and
compact. Its use requires the manuscript's local analytic/profile hypotheses
and, for OPE, the specified regular coefficient representative. All derivatives
are with respect to the relative real shape, with the center and clock fixed.
Regularity on both sides excludes totalized derivative values. -/
structure ShapeJetsAt {n : ℕ} (K : Set (Points n)) (j p : ℕ) (clock : ℝ → ℝ)
    (actual : ℝ → Points n → ℂ) (coefficient : ℕ → Points n → ℂ) : Prop where
  compact : IsCompact K
  separated : K ⊆ WilsonFamily.separated n
  smoothCoefficients (k : ℕ) (hk : k ≤ p) (x : Points n) (hx : x ∈ K) :
    ContDiffAt ℝ j (coefficient k) x
  estimate : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
    (∀ x ∈ K, ContDiffAt ℝ j (actual s) x) ∧ ∀ l ≤ j, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ l (fun y => actual s y -
        ∑ k : Fin (p+1), (clock s : ℂ)^k.val * coefficient k.val y) x‖ ≤
          A * |clock s|^(p+1)

def CorrelationShapeJetsAt (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) {n : ℕ} (K : Set (Points n)) (j p : ℕ)
    (a : Fin n → Label B) (phase : Option T.Character) (o : Spacetime) : Prop :=
  ShapeJetsAt K j p H.clock
    (fun s x => T.correlation phase (H.inputs s a) (WithLp.toLp 2 fun i => o + s • x i))
    (fun k x => S.correlation M k a x)

def OPEShapeJetsAt (M : MSbar.Coefficients B) (S : Conversion B)
    (H : Measurement B T) {n : ℕ} (K : Set (Points n)) (j h p : ℕ)
    (a : Fin n → Label B) (o : Spacetime) (out : B.sector h →ₗ[ℂ] ℂ) : Prop :=
  ShapeJetsAt K j p H.clock (fun s x => out (H.wilsonOPE s h a o x))
    (fun k x => out (S.ope M h k a x))

end YangMills.Matching
