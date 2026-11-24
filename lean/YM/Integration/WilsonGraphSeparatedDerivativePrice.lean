import YM.Integration.WilsonGraphSeparatedRegularity

noncomputable section

namespace YM.Integration.WilsonGraphSeparatedDerivativePrice

open YangMills YangMills.Matching YM.Spec YM.OPE YM.OPE.Orbits
open YM.XSpace YM.XSpace.Normalize YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2
open WilsonGraphStandaloneCorrelation
open scoped BigOperators Classical ContDiff

variable (g : YangMills.GaugeGroup)
variable (T : YM.MS.Land.MS_Data g.core (Position.OpenAxis.Plot (Press.portDeck g.core)))

include T in
/-- On the separated configuration space the ordinary ambient derivative is continuous
at every order for each submitted external conversion and mixed word. -/
theorem jetContinuous {n : ℕ} (S : Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) (m : ℕ) :
    ContinuousOn (iteratedFDeriv ℝ m (fun x => converted S k a x)) (YM.conf n) := by
  have smooth := WilsonGraphSeparatedRegularity.convertedSmooth g T S k a
  letI : IsBoundedSMul ℝ (YM.Points n) :=
    IsBoundedSMul.of_norm_smul_le (fun c x => le_of_eq (norm_smul c x))
  letI : ContinuousSMul ℝ (YM.Points n) := IsBoundedSMul.continuousSMul
  have unique : UniqueDiffOn ℝ (YM.conf n) := (YM.conf_open n).uniqueDiffOn
  have order : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have cont := smooth.continuousOn_iteratedFDerivWithin (m := m) order unique
  exact cont.congr (fun x hx =>
    (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := fun y => converted S k a y)
      m (YM.conf_open n) hx).symm)

include T in
/-- One compact price bounds the real multilinear operator norm at every point of
the submitted separated compact, with all coincident coordinate projections allowed. -/
theorem compactJet {n : ℕ} (S : Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) (m : ℕ)
    {K : Set (YangMills.Points n)} (compact : IsCompact K) (safe : K ⊆ YM.conf n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ m (fun y => converted S k a y) x‖ ≤ D := by
  have cont := (jetContinuous g T S k a m).norm.mono safe
  obtain ⟨D, upper⟩ := compact.bddAbove_image cont
  exact ⟨max 0 D, le_max_left _ _, fun x hx =>
    (upper (Set.mem_image_of_mem _ hx)).trans (le_max_right _ _)⟩

include T in
/-- The same price pays every submitted real direction and bounded complex scalar
covector. The empty direction product gives the zeroth-order assertion. -/
theorem directionsAndDual {n : ℕ} (S : Conversion (maxwellReference g)) (k : ℕ)
    (a : Fin n → WilsonGraphStandaloneCorrelation.Label g) (m : ℕ)
    {K : Set (YangMills.Points n)} (compact : IsCompact K) (safe : K ⊆ YM.conf n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ K, ∀ (v : Fin m → YangMills.Points n) (φ : ℂ →L[ℂ] ℂ),
      ‖φ ((iteratedFDeriv ℝ m (fun y => converted S k a y) x) v)‖ ≤
        ‖φ‖ * (D * ∏ i, ‖v i‖) := by
  obtain ⟨D, positive, bound⟩ := compactJet g T S k a m compact safe
  refine ⟨D, positive, ?_⟩
  intro x hx v φ
  refine (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact ((iteratedFDeriv ℝ m (fun y => converted S k a y) x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (bound x hx) (Finset.prod_nonneg fun i _ => norm_nonneg _))

include T in
/-- A single price applies simultaneously to a submitted finite family of mixed
words on this compact before choosing the point, directions, or output covector. -/
theorem finiteFamily {ι : Type*} [Fintype ι] {n : ℕ} (S : Conversion (maxwellReference g))
    (k : ℕ) (word : ι → Fin n → WilsonGraphStandaloneCorrelation.Label g) (m : ℕ)
    {K : Set (YangMills.Points n)} (compact : IsCompact K) (safe : K ⊆ YM.conf n) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j x, x ∈ K →
      ∀ (v : Fin m → YangMills.Points n) (φ : ℂ →L[ℂ] ℂ),
        ‖φ ((iteratedFDeriv ℝ m (fun y => converted S k (word j) y) x) v)‖ ≤
          ‖φ‖ * (D * ∏ i, ‖v i‖) := by
  classical
  choose D positive bound using fun j : ι => directionsAndDual g T S k (word j) m compact safe
  refine ⟨∑ j, D j, Finset.sum_nonneg (fun j _ => positive j), ?_⟩
  intro j x hx v φ
  refine (bound j x hx v φ).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ => positive i) (Finset.mem_univ j))
    (Finset.prod_nonneg fun i _ => norm_nonneg _)

end YM.Integration.WilsonGraphSeparatedDerivativePrice

